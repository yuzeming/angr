from collections import defaultdict
from typing import List, Tuple, Optional, Dict, Set
import logging
import copy
from itertools import combinations
import itertools

import networkx
import networkx as nx

from ailment.block import Block
from ailment.statement import Statement, ConditionalJump, Jump, Assignment
from ailment.expression import Const, Register

from ... import AnalysesHub
from .optimization_pass import OptimizationPass, OptimizationPassStage
from ..utils import to_ail_supergraph
from ....utils.graph import dominates


_l = logging.getLogger(name=__name__)


#
# Utils
#

def find_block_by_similarity(block, graph, node_list=None):
    nodes = node_list if node_list else list(graph.nodes())
    similar_blocks = []
    for other_block in nodes:
        if similar(block, other_block, graph=graph):
            similar_blocks.append(other_block)

    if len(similar_blocks) > 1:
        print("WARNING: found multiple similar blocks")

    return similar_blocks[0]


def find_block_by_addr(graph: networkx.DiGraph, addr, insn_addr=False):
    if insn_addr:
        def _get_addr(b): return b.statements[0].tags["ins_addr"]
    else:
        def _get_addr(b): return b.addr

    for block in graph.nodes():
        if _get_addr(block) == addr:
            break
    else:
        block = None
        raise Exception("The block is not in the graph!")

    return block


def similar(ail_obj1, ail_obj2, graph: nx.DiGraph = None, partial=False):
    if type(ail_obj1) is not type(ail_obj2):
        return False

    # AIL Blocks
    if isinstance(ail_obj1, Block):
        if len(ail_obj1.statements) != len(ail_obj2.statements):
            return False

        for stmt1, stmt2 in zip(ail_obj1.statements, ail_obj2.statements):
            if not similar(stmt1, stmt2, graph=graph):
                return False
        else:
            return True

    # AIL Statements
    elif isinstance(ail_obj1, Statement):
        # ConditionalJump Handler
        if isinstance(ail_obj1, ConditionalJump):
            # try a simple compare
            liked = ail_obj1.likes(ail_obj2)
            if liked or not graph:
                return liked

            # must use graph to know
            for attr in ["true_target", "false_target"]:
                t1, t2 = getattr(ail_obj1, attr).value, getattr(ail_obj2, attr).value
                t1_blk, t2_blk = find_block_by_addr(graph, t1), find_block_by_addr(graph, t2)

                # skip full checks when partial checking is on
                if partial and t1_blk.statements[0].likes(t2_blk.statements[0]):
                    continue

                if not similar(t1_blk, t2_blk, graph=graph):
                    return False
            else:
                return True

        # Generic Statement Handler
        else:
            return ail_obj1.likes(ail_obj2)
    else:
        return False


def sub_lists(seq):
    lists = [[]]
    for i in range(len(seq) + 1):
        for j in range(i):
            lists.append(seq[j: i])
    return lists


def kmp_search_ail_obj(search_pattern, stmt_seq, graph=None, partial=False):
    """
    Uses the Knuth-Morris-Pratt algorithm for searching.
    Found: https://code.activestate.com/recipes/117214/.

    Returns a generator of positions, which will be empty if its not found.
    """
    # allow indexing into pattern and protect against change during yield
    search_pattern = list(search_pattern)

    # build table of shift amounts
    shifts = [1] * (len(search_pattern) + 1)
    shift = 1
    for pos in range(len(search_pattern)):
        while shift <= pos and not similar(search_pattern[pos], search_pattern[pos - shift], graph=graph, partial=partial):
            shift += shifts[pos - shift]
        shifts[pos + 1] = shift

    # do the actual search
    start_pos = 0
    match_len = 0
    for c in stmt_seq:
        while match_len == len(search_pattern) or match_len >= 0 and \
                not similar(search_pattern[match_len], c, graph=graph, partial=partial):
            start_pos += shifts[match_len]
            match_len -= shifts[match_len]
        match_len += 1
        if match_len == len(search_pattern):
            yield start_pos


def ail_block_from_stmts(stmts, idx=None) -> Optional[Block]:
    if not stmts:
        return None

    first_stmt = stmts[0]

    return Block(
        first_stmt.tags['ins_addr'],
        0,
        statements=stmts,
        idx=idx or 1,
    )


def deepcopy_ail_condjump(stmt: ConditionalJump, idx=1):
    true_target: Const = stmt.true_target
    false_target: Const = stmt.false_target
    tags = stmt.tags.copy()

    return ConditionalJump(
        idx,
        stmt.condition.copy(),
        Const(1, true_target.variable, true_target.value, true_target.bits, **true_target.tags.copy()),
        Const(1, false_target.variable, false_target.value, false_target.bits, **false_target.tags.copy()),
        **tags
    )


def replace_node(old_node: Block, new_node: Block, old_graph: nx.DiGraph, new_graph: nx.DiGraph,
                 fix_successors=True, fix_predecessors=True) -> nx.DiGraph:

    # get layout in the old graph
    old_succ, old_preds = list(old_graph.successors(old_node)), list(old_graph.predecessors(old_node))

    #
    # Successors
    #

    if fix_successors:
        if len(old_succ) == 1:
            new_graph.add_edge(new_node, old_succ[0])
        elif len(old_succ) == 2:
            old_if_stmt: ConditionalJump = old_node.statements[-1]
            new_if_stmt: ConditionalJump = new_node.statements[-1]

            true_target = old_succ[0] if old_succ[0].addr == old_if_stmt.true_target.value \
                else old_succ[1]
            false_target = old_succ[1] if true_target != old_succ[1] \
                else old_succ[0]

            new_if_stmt.true_target.value = true_target.addr
            new_if_stmt.true_target.value = false_target.addr

            new_graph.add_edge(new_node, true_target)
            new_graph.add_edge(new_node, false_target)
        else:
            new_graph.add_node(new_node)

    #
    # Predecessors
    #

    if fix_predecessors:
        for pred in old_preds:
            if isinstance(pred.statements[-1], ConditionalJump):
                if_stmt = pred.statements[-1]
                for attr in ["true_target", "false_target"]:
                    target = getattr(if_stmt, attr)
                    if target.value == old_node.addr:
                        target.value = new_node.addr
                        new_graph.add_edge(pred, new_node)
            else:
                new_graph.add_edge(pred, new_node)

    return new_graph


def split_ail_block(block, split_idx, split_len) -> Tuple[Optional[Block], Optional[Block], Optional[Block]]:
    pre_split = ail_block_from_stmts(block.statements[:split_idx])
    merge_split = ail_block_from_stmts(block.statements[split_idx:split_idx + split_len])
    post_split = ail_block_from_stmts(block.statements[split_idx + split_len:])

    return pre_split, merge_split, post_split


def lcs_ail_stmts(blocks, graph=None, partial=False):
    print(f"RUNNING LCS ON {blocks}")
    # generate the lcs for each pair
    lcs_list = list()
    for b0, b1 in combinations(blocks, 2):
        stmts0, stmts1 = b0.statements, b1.statements
        stmt_seqs = sub_lists(stmts0)
        matches = [(stmt_seq, list(kmp_search_ail_obj(stmt_seq, stmts1, graph=graph, partial=partial))) for stmt_seq in stmt_seqs]
        match_seq, match_pos_in_1 = max(matches, key=lambda m: len(m[0]) if len(m[1]) > 0 else -1)
        lcs_list.append(match_seq)

    # take each pairs lcs and find the lcs of those lcs (to get the overall lcs)
    #print(f"LCS LIST: {lcs_list}")
    not_fixed = True
    while not_fixed:
        not_fixed = False
        common_lcs = list()

        # stop once we only have one
        if len(lcs_list) == 1:
            if lcs_list[0] is None:
                return None, {}

            break

        # check each lcs against the others in the list
        for lcs in lcs_list:
            if all(True if len(list(kmp_search_ail_obj(lcs, other_lcs, graph=graph, partial=partial))) > 0 else False for other_lcs in lcs_list):
                # assure we are not re-adding the same lcs
                for clcs in common_lcs:
                    if len(lcs) == len(clcs) and all(similar(s1, s2) for s1, s2 in zip(lcs, clcs)):
                        break
                else:
                    common_lcs.append(lcs)
                    not_fixed |= True

        lcs_list = common_lcs
        _l.info(f"LCS LIST ITERATION: {lcs_list}")

    # finally, locate the lcs in all blocks
    try:
        lcs = lcs_list[0]
    except IndexError:
        return None, None

    block_idxs = {}
    for block in blocks:
        block_idxs[block] = list(kmp_search_ail_obj(lcs, block.statements, graph=graph, partial=partial))[0]

    return lcs, block_idxs


class BlockDiff:
    def __init__(self, lcs, blk0, blk0_lcs_idx, blk1, blk1_lcs_idx):
        self.differs = False
        self.lcs = lcs
        self.blk0 = blk0
        self.blk0_lcs_idx = blk0_lcs_idx
        self.blk1 = blk1
        self.blk1_lcs_idx = blk1_lcs_idx

        self._check_differ()

    def _check_differ(self):
        if (len(self.blk0.statements) != len(self.lcs) + self.blk0_lcs_idx) or \
                (len(self.blk1.statements) != len(self.lcs) + self.blk1_lcs_idx):
            self.differs = True


def ail_graph_diff(start_blk0: Block, start_blk1: Block, graph: nx.DiGraph, partial=True) -> List[BlockDiff]:
    """
    Takes the start blocks of two sub-graphs that reside in graph. It returns a list of blocks that are similar
    in the subgraphs. The tuple will provide the blocks that are similar in both graphs.

    Theory on Algorithm:
    If we want to find how two graphs compare we just need to iterate both graphs nodes in the same order. When
    we come to a ConditionalJump, we just align the search by using the true and false targets. The graph can start
    with the first block being different in start statements, but all blocks after it must be exact copies.
    """
    # sanity check on blocks actually being the literally same block
    if start_blk0 == start_blk1:
        return [] #[BlockDiff(start_blk0.statements, start_blk0, 0, start_blk1, 0)]

    blocks = [start_blk0, start_blk1]
    lcs, block_idxs = lcs_ail_stmts(blocks, graph=graph, partial=partial)
    if not lcs:
        return []

    lcs_len = len(lcs)
    block_diff = BlockDiff(lcs, start_blk0, block_idxs[start_blk0], start_blk1, block_idxs[start_blk1])

    # check if both blocks end in the same statements
    if not all(lcs_len + block_idxs[block] == len(block.statements) for block in blocks):
        return [block_diff]

    # it's an actual graph, do the search
    successors = {
        start_blk0: list(graph.successors(start_blk0)),
        start_blk1: list(graph.successors(start_blk1))
    }

    if len(successors[start_blk0]) == len(successors[start_blk1]) == 1:
        # check how the successors differ
        return [block_diff] + ail_graph_diff(successors[start_blk0][0], successors[start_blk1][0], graph, partial=partial)
    elif len(successors[start_blk0]) == len(successors[start_blk1]) == 2:
        targets = {}
        for block in blocks:
            if_stmt = block.statements[-1]
            true_target = successors[block][0] if successors[block][0].addr == if_stmt.true_target.value \
                else successors[block][1]
            false_target = successors[block][1] if true_target != successors[block][1] \
                else successors[block][0]
            targets[block] = {"true": true_target, "false": false_target}

        # check how the true and false target successors differ
        return [block_diff] + \
            ail_graph_diff(targets[start_blk0]["true"], targets[start_blk1]["true"], graph, partial=partial) + \
            ail_graph_diff(targets[start_blk0]["false"], targets[start_blk1]["false"], graph, partial=partial)

    # if none of the successors amt match, we end the search here
    return [block_diff]


def lcs_ail_graph_blocks(start_blocks: List[Block], graph: nx.DiGraph):
    """
    This algorithm will take a series of blocks, that should be the head of a graph, and attempt to find
    a common subgraph among them.

    @param start_blocks:
    @param graph:
    @return:
    """

    split_to_orig_map = {}
    orig_to_split_map = {}

    def _similar_blocks_from_graph_diff(graph_diff: List[BlockDiff]):
        similar_blocks = []
        for diff in graph_diff:
            # if there is a differ we need to split it
            if diff.differs:
                pre, b0, post = split_ail_block(diff.blk0, diff.blk0_lcs_idx, len(diff.lcs))
                pre_1, b1, post_1 = split_ail_block(diff.blk1, diff.blk1_lcs_idx, len(diff.lcs))
                split_to_orig_map[b0] = diff.blk0
                split_to_orig_map[b1] = diff.blk0
                orig_to_split_map[diff.blk0] = (pre, b0, post)
                orig_to_split_map[diff.blk1] = (pre_1, b1, post_1)
            else:
                b0 = diff.blk0
            similar_blocks.append(b0)

        return similar_blocks

    # collect the difference in every graph
    similar_graph_diffs = []
    full_diffs = []
    for blk0, blk1 in combinations(start_blocks, 2):
        block_diffs = ail_graph_diff(blk0, blk1, graph)
        similar_graph_diffs.append(_similar_blocks_from_graph_diff(block_diffs))
        full_diffs.append(block_diffs)

    # find the lcs of the graph diffs
    not_fixed = True
    while not_fixed:
        not_fixed = False
        common_graph_diffs = list()

        # stop once we only have one seq
        if len(similar_graph_diffs) == 1:
            break

        # check each diff against the others
        for graph_diff in similar_graph_diffs:
            all_match = True
            for other_diff in similar_graph_diffs:
                # skip the same diff (not like similar)
                if graph_diff == other_diff:
                    continue

                if len(graph_diff) > len(other_diff):
                    all_match = False
                    break

                # iterate each block in each diff
                for i, block in enumerate(graph_diff):
                    # both the start and end can have a split
                    if i == 0 or i == len(graph_diff)-1:
                        lcs, _ = lcs_ail_stmts([block, other_diff[i]], graph=graph)
                        if not lcs:
                            all_match = False
                            break
                    else:
                        if not similar(block, other_diff[i]):
                            all_match = False
                            break

            if all_match:
                # assure no duplicates exist in set
                for cgd in common_graph_diffs:
                    if len(graph_diff) == len(cgd) and \
                            all(similar(s1, s2, graph=graph) for s1, s2 in zip(graph_diff, cgd)):
                        break
                else:
                    common_graph_diffs.append(graph_diff)
                    not_fixed = True

        similar_graph_diffs = common_graph_diffs

    # create the subgraph from the original graph
    common_graph_diff = similar_graph_diffs[0]
    common_graph_blocks = [blk for blk in common_graph_diff if graph.has_node(blk)]
    split_blocks = [blk for blk in common_graph_diff if blk not in common_graph_blocks]
    if not common_graph_blocks:
        common_graph: nx.DiGraph = nx.DiGraph()
        common_graph.add_nodes_from(split_blocks)
    # needs correcting for split blocks
    else:
        common_graph = nx.subgraph(graph, common_graph_blocks)
        common_graph = common_graph.copy()

        for split_block in split_blocks:
            og_block = split_to_orig_map[split_block]

            # start with tail splits
            if any(common_graph.has_node(pred) for pred in graph.predecessors(og_block)):
                common_graph = replace_node(og_block, split_block, graph, common_graph, fix_successors=False)

            # end with head splits
            elif any(common_graph.has_node(succ) for succ in graph.successors(og_block)):
                common_graph = replace_node(og_block, split_block, graph, common_graph, fix_predecessors=False)

    # finally, find the start and ends of each splits
    removable_blocks = set()
    for diff in full_diffs:
        for block_diff in diff:
            removable_blocks.add(block_diff.blk0)
            removable_blocks.add(block_diff.blk1)

    return common_graph, orig_to_split_map, removable_blocks


class MergeTarget:
    def __init__(self, predecessor_map: Dict[Block, List[Block]], pre_block_map: Dict[Block, Block],
                 post_block_map: Dict[Block, Block], successor_map: Dict[Block, List[Block]]
                 ):
        # [start_block, predecessor]
        self.predecessor_map = predecessor_map
        # [orig_block, pre_block]
        self.pre_block_map = pre_block_map
        # [end_block, post_block]
        self.post_block_map = post_block_map
        # [end_block, successor]
        self.successor_map = successor_map

    def __str__(self):
        return f"<MergeTarget: {{\npreds[{self.predecessor_map}],\npre_blocks[{self.pre_block_map}],\n"\
               f"post_blocks[{self.post_block_map}],\nsuccs[{self.successor_map}]\n}}"

    def __repr__(self):
        return str(self)


#
# Merger Optimization
#

def remove_redundant_jumps(graph: nx.DiGraph):
    while True:
        remove_queue = list()
        for block in graph.nodes:
            if len(block.statements) != 1:
                continue

            stmt = block.statements[0]
            if not isinstance(stmt, (Jump, ConditionalJump)):
                continue

            succs = list(graph.successors(block))
            if len(succs) <= 0:
                continue

            # skip real ConditionalJumps (ones with two different true/false target)
            if isinstance(stmt, ConditionalJump):
                if len(succs) == 2 and stmt.true_target.value != stmt.false_target.value:
                    continue

            succ = succs[0]
            remove_queue.append(block)
            for pred in graph.predecessors(block):
                if isinstance(pred.statements[-1], ConditionalJump):
                    if_stmt = pred.statements[-1]
                    if if_stmt.true_target.value == block.addr:
                        if_stmt.true_target.value = succ.addr
                    else:
                        if_stmt.false_target.value = succ.addr

                graph.add_edge(pred, succ)

        if not remove_queue:
            break

        print(f"removing {remove_queue}")
        graph.remove_nodes_from(remove_queue)

    return graph


def remove_simple_similar_blocks(graph: nx.DiGraph):
    """
    Removes blocks that have all statements that are similar and the same successors
    @param graph:
    @return:
    """
    nodes = list(graph.nodes())
    remove_queue = list()
    for b0, b1 in itertools.combinations(nodes, 2):
        # blocks should have the same successors
        if list(graph.successors(b0)) != list(graph.successors(b1)):
            continue

        if not similar(b0, b1, graph=graph):
            continue

        remove_queue.append((b0, b1))

    for b0, b1 in remove_queue:
        if not (graph.has_node(b0) or graph.has_node(b1)):
            continue

        graph = replace_node(b0, b1, graph, graph)
        graph.remove_node(b0)

    return graph


def shared_common_conditional_dom(nodes, graph: nx.DiGraph):
    """
    Takes n nodes and returns True only if all the nodes are dominated by the same node, which must be
    a ConditionalJump

    @param nodes:
    @param graph:
    @return:
    """
    entry_blk = [node for node in graph.nodes if graph.in_degree(node) == 0][0]
    idoms = nx.algorithms.immediate_dominators(graph, entry_blk)
    dominators = [idoms[node] for node in nodes]

    for dom in dominators:
        if isinstance(dom.statements[-1], ConditionalJump) and all(dominates(idoms, dom, node) for node in nodes):
            return dom

    return None


class BlockMerger(OptimizationPass):

    ARCHES = ['AMD64', 'ARMEL', 'ARMHF', "ARMCortexM", ]
    PLATFORMS = ["cgc", "linux"]
    STAGE = OptimizationPassStage.AFTER_VARIABLE_RECOVERY

    def __init__(self, func, **kwargs):

        super().__init__(func, **kwargs)

        self.analyze()

    def _check(self):

        # TODO: More checks

        return True, {}

    #
    # Graph Utilities
    #

    def _copy_cond_graph(self, merge_start_nodes, idx=1):
        # [merge_node, nx.DiGraph: pre_graph]
        pre_graphs_maps = {}
        # [merge_node, nx.DiGraph: full_graph]
        graph_maps = {}
        # [merge_node, removed_nodes]
        removed_node_map = defaultdict(list)

        # create a subgraph for every merge_start and the dom
        shared_conditional_dom = shared_common_conditional_dom(merge_start_nodes, self.copy_graph)
        for merge_start in merge_start_nodes:
            paths_between = nx.all_simple_paths(self.copy_graph, source=shared_conditional_dom, target=merge_start)
            nodes_between = {node for path in paths_between for node in path}
            graph_maps[merge_start] = nx.subgraph(self.copy_graph, nodes_between)

        # create remove nodes for nodes that are shared among all graphs (conditional nodes)
        for block0, graph0 in graph_maps.items():
            for node in graph0.nodes:
                for block1, graph1 in graph_maps.items():
                    if block0 == block1:
                        continue

                    if node in graph1.nodes:
                        removed_node_map[block0].append(node)

        # make the pre-graph from removing the nodes
        for block, graph in graph_maps.items():
            pre_graph = graph.copy()
            pre_graph.remove_nodes_from(removed_node_map[block])
            pre_graphs_maps[block] = pre_graph

        # make a conditional graph from any remove_nodes map (no deepcopy)
        cond_graph: nx.DiGraph = nx.subgraph(self.copy_graph, removed_node_map[merge_start_nodes[0]])

        # deep copy the graph and remove instructions that are not conditionals
        new_cond_graph = nx.DiGraph()
        orig_successors_by_insn = {
            node.statements[-1].tags['ins_addr']: list(cond_graph.successors(node)) for node in cond_graph.nodes()
        }
        orig_nodes_by_insn = {
            node.statements[-1].tags['ins_addr']: node for node in cond_graph.nodes()
        }

        # first pass: deepcopy all the nodes
        for node in cond_graph.nodes():
            # make the condition the only part of the node
            new_cond_graph.add_node(ail_block_from_stmts([deepcopy_ail_condjump(node.statements[-1], idx=idx)]))

        # second pass: correct all the old edges
        for node in new_cond_graph.nodes():
            if_stmt = node.statements[-1]

            # make new edges
            old_sucs = orig_successors_by_insn[node.addr]
            old_node = orig_nodes_by_insn[node.addr]
            old_true = old_node.statements[-1].true_target.value
            old_false = old_node.statements[-1].false_target.value
            for old_suc in old_sucs:
                new_suc = find_block_by_addr(new_cond_graph, old_suc.statements[-1].tags['ins_addr'])

                # correct the conditional
                if old_true == old_suc.addr:
                    if_stmt.true_target.value = new_suc.addr

                if old_false == old_suc.addr:
                    if_stmt.false_target.value = new_suc.addr

                # add the edge
                new_cond_graph.add_edge(node, new_suc)

        # correct edges that just go to code
        #breakpoint()
        for node in new_cond_graph.nodes:
            if_stmt = node.statements[-1]
            for attr in ["true_target", "false_target"]:
                target = getattr(if_stmt, attr)
                try:
                    curr_succ = find_block_by_addr(self.copy_graph, target.value)
                except Exception as e:
                    continue

                for new_target, pre_graph in pre_graphs_maps.items():
                    if pre_graph.has_node(curr_succ):
                        target.value = new_target.addr
                        break

        return new_cond_graph, pre_graphs_maps

    #
    # Analysis stages
    #

    def _find_initial_candidates(self) -> List[Tuple[Block, Block]]:
        initial_candidates = list()
        for b0, b1 in combinations(self.copy_graph.nodes, 2):
            # check if these nodes share any stmt in common
            stmt_in_common = False
            for stmt0 in b0.statements:
                # jumps don't count
                if isinstance(stmt0, Jump):
                    continue

                # register-only assignments don't count, one must be a const or expression
                if isinstance(stmt0, Assignment) and \
                        (isinstance(stmt0.src, Register) and isinstance(stmt0.dst, Register)):
                    continue

                for stmt1 in b1.statements:
                    if stmt0.likes(stmt1):
                        stmt_in_common = True
                        break

                if stmt_in_common:
                    pair = (b0, b1)
                    # only append pairs that share a dominator
                    if shared_common_conditional_dom(pair, self.copy_graph) is not None:
                        initial_candidates.append(pair)
                    else:
                        print(f"### COMMON PAIR {pair} don't share a common Conditional Dom")

                    break

        return list(set(initial_candidates))

    def _filter_candidates(self, candidates):
        """
        Preform a series of filters on the candidates to reduce the fast set to an assured set of
        the duplication case we are searching for.
        """

        #
        # First locate all the pairs that may actually be in a merge-graph of one of the already existent
        # pairs. This will look like a graph diff having a block existent in its list of nodes.
        #

        diffs_list = {
            (b0, b1): ail_graph_diff(b0, b1, self.copy_graph) for b0, b1 in candidates
        }
        while True:
            removal_queue = list()
            for pair0, diffs in diffs_list.items():
                if pair0 in removal_queue:
                    continue

                all_blks_in_diff = list(itertools.chain.from_iterable([[diff.blk0, diff.blk1] for diff in diffs]))
                for pair1 in candidates:
                    if pair1 == pair0:
                        continue

                    if all(blk in all_blks_in_diff for blk in pair1):
                        removal_queue.append(pair1)

            if len(removal_queue) == 0:
                break

            print(f"removing descendant pairs: {removal_queue}")
            for pair in set(removal_queue):
                candidates.remove(pair)

        #
        # Now, merge pairs that may actually be n-pairs. This will look like multiple pairs having a single
        # block in common, and have one or more statements in common.
        #

        not_fixed = True
        while not_fixed:
            not_fixed = False
            queued = set()
            merged_candidates = []

            # no merging needs to be done, there is only one candidate left
            if len(candidates) == 1:
                break

            for can0 in candidates:
                # skip candidates being merged
                if can0 in queued:
                    continue

                # make sure we dont try to merge a singleton
                for blk in can0:
                    for can1 in candidates:
                        if can0 == can1 or can1 in queued:
                            continue

                        # merge and queue
                        lcs, _ = lcs_ail_stmts(can0 + can1)
                        if blk in can1 and lcs:
                            print(f"MERGING {can0} into {can1}")
                            merged_candidates.append(tuple(set(can0 + can1)))
                            queued.add(can0)
                            queued.add(can1)
                            not_fixed |= True
                            break

            remaining_candidates = []
            for can in candidates:
                for m_can in merged_candidates:
                    if not all(blk not in m_can for blk in can):
                        break
                else:
                    remaining_candidates.append(can)

            candidates = merged_candidates + remaining_candidates
            print(f"filtered now: {candidates}")

        candidates = list(set(candidates))
        return candidates

    def generate_merge_targets(self, blocks, graph: nx.DiGraph) -> \
            Tuple[nx.DiGraph, Dict[int, MergeTarget], Set[Block]]:
        """
        We locate the merge target graph as well as the places they differ.
        Consider merge graphs:
        Gx:    [A, B, C] -> [D,E] -> [F]
        Gy:    [C] -> [D,E] -> [F, E]

        Each merge graph has pre-blocks and post-blocks that will be split off
        Gx-Pre-Blocks: [[A,B]]
        Gy-Pre-Blocks: [None]
        Gx-Post-Blocks: [None]
        Gy-Post-Blocks: [[E]]

        Plan:
        1. Do two graphs at a time and try to find the longest common block seq

        @param blocks:
        @param graph:
        @return:
        """
        merge_targets: Dict[Block, MergeTarget] = {}
        merge_graph, original_block_map, removable_blocks = lcs_ail_graph_blocks(blocks, graph)
        merge_ends = [node for node in merge_graph.nodes if merge_graph.out_degree(node) == 0]
        secondary_remove_set = set() #TODO: this is bad

        # pre blocks
        for block in blocks:
            pre, _, post = original_block_map[block] if block in original_block_map else (None, None, None)
            merge_targets[block] = MergeTarget(
                {pre: list(graph.predecessors(block))},
                {pre: block},
                {},
                {},
            )

        block_descendants = {block: nx.descendants(graph, block).union({block}) for block in blocks}
        for orig_block, split in original_block_map.items():
            pre, merge, post = split
            for block, descendants in block_descendants.items():
                merge_end = find_block_by_similarity(merge, merge_graph, node_list=merge_ends)
                if orig_block in descendants:
                    merge_targets[block].post_block_map[merge_end] = post
                    # get all the blocks between
                    paths_between = nx.all_simple_paths(graph, source=block, target=orig_block)
                    secondary_remove_set.update({node for path in paths_between for node in path})
                    secondary_remove_set.update({orig_block, block})

                    merge_targets[block].successor_map[merge_end] = list(graph.successors(orig_block))

        if secondary_remove_set:
            removable_blocks = secondary_remove_set

        return merge_graph, merge_targets, removable_blocks

    def _analyze(self, cache=None):
        """
        Entry analysis routine that will trigger the other analysis stages
        """
        allowed_depth = 10
        curr_depth = 0
        self.out_graph = remove_redundant_jumps(to_ail_supergraph(self._graph))
        while True:
            if curr_depth >= allowed_depth:
                raise Exception("Exceeded max depth allowed for duplication fixing")

            curr_depth += 1

            # do all writes on out_graph and all reads on copy_graph
            self.copy_graph = self.out_graph.copy()

            candidates = self._find_initial_candidates()
            if not candidates:
                print("There are no duplicate statements in this function")
                return

            candidates = self._filter_candidates(candidates)
            if not candidates:
                print("There are no duplicate blocks in this function")
                return

            print(f"CANDIDATES FOUND: {candidates}")
            candidates = sorted(candidates, key=lambda x: len(x))

            for blocks in candidates:
                # 1: locate the longest duplicate sequence in a graph and split it at the merge
                merge_graph, merge_targets, removable_nodes = self.generate_merge_targets(blocks, self.copy_graph)
                merge_start = [node for node in merge_graph.nodes if merge_graph.in_degree(node) == 0][0]
                merge_ends = [node for node in merge_graph.nodes if merge_graph.out_degree(node) == 0]

                # 2: destroy the old blocks that will be merged and add the new merge graph
                print(f"DESTROYING NODES: {removable_nodes}")
                self.out_graph.remove_nodes_from(removable_nodes)
                self.out_graph = nx.compose(self.out_graph, merge_graph)

                # 3: clone the conditional graph
                # every end node in the merge graph needs a conditional graph to copy and assign
                merge_end_to_cond_graph = {}
                # guarantees at least a single run
                for i, merge_end in enumerate(merge_ends):
                    cond_graph, pre_graph_map = self._copy_cond_graph(blocks, idx=i+1)
                    root_cond = [node for node in cond_graph.nodes if cond_graph.in_degree(node) == 0][0]
                    merge_end_to_cond_graph[merge_end] = (root_cond, cond_graph)

                # 4: replace the edges from the preds to the pre block
                for _, merge_target in merge_targets.items():
                    for pre_blk, old_blk in merge_target.pre_block_map.items():
                        new_block = pre_blk if pre_blk else merge_start
                        for pred in merge_target.predecessor_map[pre_blk]:
                            if isinstance(pred.statements[-1], ConditionalJump):
                                if_stmt: ConditionalJump = pred.statements[-1]
                                for attr in ["true_target", "false_target"]:
                                    target = getattr(if_stmt, attr)
                                    if target.value == old_blk.addr:
                                        target.value = new_block.addr

                            self.out_graph.add_edge(pred, new_block)

                        if pre_blk:
                            self.out_graph.add_edge(pre_blk, merge_start)

                # 5: make the merge graph ends point to conditional graph copies
                for merge_end, cond_graph_info in merge_end_to_cond_graph.items():
                    cond_root, cond_graph = cond_graph_info
                    self.out_graph = nx.compose(self.out_graph, cond_graph)
                    self.out_graph.add_edge(merge_end, cond_root)

                # 6: make the new conditionals point to the post-block
                for merge_end, cond_graph_info in merge_end_to_cond_graph.items():
                    cond_root, cond_graph = cond_graph_info

                    for block, merge_target in merge_targets.items():
                        post_blk = merge_target.post_block_map[merge_end]
                        new_block = post_blk if post_blk else merge_target.successor_map[merge_end][0]

                        for cond in cond_graph.nodes:
                            if_stmt: ConditionalJump = cond.statements[-1]
                            for attr in ["true_target", "false_target"]:
                                target = getattr(if_stmt, attr)
                                if target.value == block.addr:
                                    target.value = new_block.addr
                                    self.out_graph.add_edge(cond, new_block)


                # 8: make the post blocks continue to the next successors
                for _, merge_target in merge_targets.items():
                    for merge_end, post_block in merge_target.post_block_map.items():
                        if not post_block:
                            continue

                        for suc in merge_target.successor_map[merge_end]:
                            self.out_graph.add_edge(post_block, suc)


                # 9???: fix the merge nodes
                for node in merge_graph.nodes:
                    if not isinstance(node.statements[-1], ConditionalJump):
                        continue

                    if_stmt = node.statements[-1]
                    for attr in ["true_target", "false_target"]:
                        target = getattr(if_stmt, attr)
                        all_succ = [suc.addr for suc in self.out_graph.successors(node)]

                        if target.value in all_succ:
                            continue

                        new_succ = find_block_by_addr(self.out_graph, target.value)
                        self.out_graph.add_edge(node, new_succ)

                self.out_graph = remove_redundant_jumps(self.out_graph)
                return


AnalysesHub.register_default("BlockMerger", BlockMerger)
