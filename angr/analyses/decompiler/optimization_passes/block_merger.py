from collections import defaultdict
from typing import List, Tuple, Optional, Dict, Set, Union
import logging
from itertools import combinations
import itertools

import networkx
import networkx as nx

from ailment.block import Block
from ailment.statement import Statement, ConditionalJump, Jump, Assignment
from ailment.expression import Const, Register

from ... import AnalysesHub
from .optimization_pass import OptimizationPass, OptimizationPassStage
from ..region_identifier import RegionIdentifier, GraphRegion, MultiNode
from ..utils import to_ail_supergraph
from ....utils.graph import dominates


_l = logging.getLogger(name=__name__)


#
# Graph Utils
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


def clone_graph_with_splits(graph_param: nx.DiGraph, split_map_param):
    split_map = {
        block.addr: new_node for block, new_node in split_map_param.items()
    }
    graph = copy_graph_and_nodes(graph_param)
    # this loop will continue to iterate until there are no more
    # nodes found in the split_map to change
    while True:
        for node in graph.nodes():
            try:
                new_node = split_map[node.addr]
                del split_map[node.addr]
            except KeyError:
                continue

            break
        else:
            break

        graph.add_node(new_node)
        for pred in graph.predecessors(node):
            last_stmt = pred.statements[-1]
            pred.statements[-1] = correct_jump_targets(
                last_stmt,
                {node.addr: new_node.addr},
                new_stmt=True
            )

            graph.add_edge(pred, new_node)

        for succ in graph.successors(node):
            graph.add_edge(new_node, succ)

        graph.remove_node(node)

    for node in graph.nodes():
        last_stmt = node.statements[-1]
        node.statements[-1] = correct_jump_targets(
            last_stmt,
            {orig_addr: new.addr for orig_addr, new in split_map.items()},
            new_stmt=True
        )

    return graph


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

    if not fix_successors and not fix_predecessors:
        new_graph.add_node(new_node)

    return new_graph


def bfs_list_blocks(start_block: Block, graph: nx.DiGraph):
    blocks = []
    bfs = list(nx.bfs_successors(graph, start_block, depth_limit=10))
    for blk_tree in bfs:
        source, children = blk_tree

        if len(children) == 1:
            blocks += children
        elif len(children) == 2:
            if_stmt: ConditionalJump = source.statements[-1]
            if children[0].addr == if_stmt.true_target.value:
                blocks += [children[0], children[1]]
            else:
                blocks += [children[1], children[0]]

    blocks = [start_block] + blocks
    return blocks


def copy_graph_and_nodes(graph: nx.DiGraph) -> nx.DiGraph:
    new_graph = networkx.DiGraph()
    for node in graph.nodes:
        new_graph.add_node(ail_block_from_stmts(node.statements, block_addr=node.addr))

    for edge in graph.edges:
        old_b0, old_b1 = edge
        b0, b1 = find_block_by_addr(new_graph, old_b0.addr), find_block_by_addr(new_graph, old_b1.addr)
        new_graph.add_edge(b0, b1)

    return new_graph


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
    """
    ancestors = {
        node: list(nx.ancestors(graph, node)) for node in nodes
    }

    # no node for merging can be an ancestor to the other
    for node in nodes:
        other_ancestors = itertools.chain.from_iterable([ances for n, ances in ancestors.items() if n != node])
        if node in other_ancestors:
          return None
    """

    # first check if any of the node pairs could be a dominating loop
    for b0, b1 in itertools.combinations(nodes, 2):
        if dominates(idoms, b0, b1) or dominates(idoms, b0, b1):
            return None

    node = nodes[0]
    node_level = [node]
    seen_nodes = set()
    while node_level:
        # check if any of the nodes on the current level are dominaters to all nodes
        for cnode in node_level:
            if isinstance(cnode.statements[-1], ConditionalJump) \
                    and all(dominates(idoms, cnode, node) for node in nodes) \
                    and cnode not in nodes:
                return cnode

        # if no dominators found, move up a level
        seen_nodes.update(set(node_level))
        next_level = list(itertools.chain.from_iterable([list(graph.predecessors(cnode)) for cnode in node_level]))
        # only add nodes we have never seen
        node_level = set(next_level).difference(seen_nodes)

    else:
        return None


#
# AIL Helpers
#


def similar(ail_obj1, ail_obj2, graph: nx.DiGraph = None, partial=True):
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
                try:
                    t1_blk, t2_blk = find_block_by_addr(graph, t1), find_block_by_addr(graph, t2)
                except Exception:
                    return False

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


def ail_block_from_stmts(stmts, idx=None, block_addr=None) -> Optional[Block]:
    if not stmts:
        return None

    first_stmt = stmts[0]

    return Block(
        first_stmt.tags['ins_addr'] if not block_addr else block_addr,
        0,
        statements=[stmt for stmt in stmts],
        idx=idx or 1,
    )


def split_ail_block(block, split_idx, split_len) -> Tuple[Optional[Block], Optional[Block], Optional[Block]]:
    if split_len == len(block.statements):
        return None, block, None

    pre_split = ail_block_from_stmts(block.statements[:split_idx])
    merge_split = ail_block_from_stmts(block.statements[split_idx:split_idx + split_len])
    post_split = ail_block_from_stmts(block.statements[split_idx + split_len:])

    return pre_split, merge_split, post_split


def deepcopy_ail_jump(stmt: Jump, idx=1):
    target: Const = stmt.target
    tags = stmt.tags.copy()

    return Jump(
        idx,
        Const(1, target.variable, target.value, target.bits, **target.tags.copy()),
        **tags
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


def deepcopy_ail_anyjump(stmt: Union[Jump, ConditionalJump], idx=1):
    if isinstance(stmt, Jump):
        return deepcopy_ail_jump(stmt, idx=idx)
    elif isinstance(stmt, ConditionalJump):
        return deepcopy_ail_condjump(stmt, idx=idx)
    else:
        raise Exception("Attempting to deepcopy non-jump stmt, likely happen to a "
                        "block ending in no jump. Place a jump there to fix it.")


def correct_jump_targets(stmt, replacement_map: Dict[int, int], new_stmt=False):
    if not replacement_map:
        return stmt

    if isinstance(stmt, ConditionalJump):
        cond_stmt = deepcopy_ail_condjump(stmt) if new_stmt else stmt
        true_target, false_target = cond_stmt.true_target, cond_stmt.false_target

        if isinstance(true_target, Const) and true_target.value in replacement_map:
            true_target.value = replacement_map[true_target.value]

        if isinstance(false_target, Const) and false_target.value in replacement_map:
            false_target.value = replacement_map[false_target.value]

        return cond_stmt
    elif isinstance(stmt, Jump):
        jump_stmt = deepcopy_ail_jump(stmt) if new_stmt else stmt
        target = jump_stmt.target

        if isinstance(target, Const) and target.value in replacement_map:
            target.value = replacement_map[target.value]

        return jump_stmt
    else:
        return stmt


#
# Longest Common Substring Search Helpers/Functions
#

def _kmp_search_ail_obj(search_pattern, stmt_seq, graph=None, partial=True):
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


def stmts_pos_in_other(stmts, other, graph=None):
    """
    Equivalent to asking:
    stmts in other

    @return: None or int (position start in other)
    """
    positions = list(_kmp_search_ail_obj(stmts, other, graph=graph))

    if len(positions) == 0:
        return None

    top_pos = positions.pop()
    return top_pos


def stmt_in_other(stmts, other, graph=None):
    """
    Returns True if the stmts (a list of Statement) is found as a subsequence in other

    @return:
    """

    if stmts_pos_in_other(stmts, other, graph=graph) is not None:
        return True

    return False


def longest_ail_subseq(stmts_list, graph=None):
    """
    Returns the LCS (a list of Statement) of the list of stmts (list of Statement).
    Returns LCS, [LCS_POS_IN_0, LCS_POS_IN_1, ..., LCS_POS_IN_N]

    @param stmts_list:
    @param graph:
    @return:
    """

    # find the longest sequence in all stmts
    subseq = []
    if len(stmts_list) <= 1:
        return stmts_list[0], 0

    if len(stmts_list[0]) > 0:
        for i in range(len(stmts_list[0])):
            for j in range(len(stmts_list[0]) - i + 1):
                if j > len(subseq) and all(stmt_in_other(stmts_list[0][i:i+j], stmts, graph=graph) for stmts in stmts_list):
                    subseq = stmts_list[0][i:i + j]

    if not subseq:
        return None, [None]*len(stmts_list)

    return subseq, [stmts_pos_in_other(subseq, stmts, graph=graph) for stmts in stmts_list]


def longest_ail_graph_subseq(block_list, graph):
    # generate a graph similarity for each pair in the provided blocks
    all_sims = [
        ail_graph_similarity(pair[0], pair[1], graph) for pair in itertools.combinations(block_list, 2)
    ]

    lcs, _ = longest_ail_subseq(all_sims, graph)
    return lcs


def ail_graph_similarity(block0: Block, block1: Block, graph: nx.DiGraph, only_blocks=False):
    b0_blocks = bfs_list_blocks(block0, graph)
    b1_blocks = bfs_list_blocks(block1, graph)
    similarity = list()

    block_splits = {b: list() for b in [block0, block1]}
    discontinuity_blocks = set()
    for i, b0 in enumerate(b0_blocks):
        # getting to a block with no matching index is grounds to stop cmp
        try:
            b1 = b1_blocks[i]
        except IndexError:
            break

        # if a block in the chain before did not end in LCS, don't follow it.
        if b0 in discontinuity_blocks or b1 in discontinuity_blocks:
            continue

        # SPECIAL CASE: b0 is b1 AND all its preds go to the same places
        if b0 is b1:
            preds = list(graph.predecessors(b0))
            all_match = True
            for pred1 in preds:
                for pred2 in preds:
                    if set(list(graph.successors(pred1))) != set(list(graph.successors(pred2))):
                        all_match = False
                        break

                if not all_match:
                    break

            if all_match:
                continue

        # find the common statements of the two
        lcs, lcs_idxs = longest_ail_subseq([b0.statements, b1.statements], graph=graph)
        if not lcs:
            break

        # verify all the blocks end in that statement or exclude its children
        for idx, b in enumerate([b0, b1]):
            if len(lcs) + lcs_idxs[idx] != len(b.statements):
                discontinuity_blocks.update(set(list(graph.successors(b))))

        # can output blocks only if needed
        similarity += lcs if not only_blocks else [(b0, b1)]

    return similarity


def ail_similarity_to_orig_blocks(orig_block, graph_similarity, graph):
    traversal_blocks = bfs_list_blocks(orig_block, graph)

    graph_sim = graph_similarity.copy()
    orig_blocks = list()
    split_blocks = {}  # [block] = (lcs, idx)
    for block in traversal_blocks:
        if not graph_sim:
            break

        lcs, lcs_idxs = longest_ail_subseq([block.statements, graph_sim[:len(block.statements)]], graph=graph)
        if block is orig_block:
            lcs_1, lcs_idxs_1 = longest_ail_subseq([graph_sim[:len(block.statements)], block.statements], graph=graph)
            if lcs_idxs_1[1] > lcs_idxs[0]:
                lcs, lcs_idxs = lcs_1, lcs_idxs_1[::-1]

        if not lcs:
            break

        orig_blocks.append(block)

        if len(lcs) != len(block.statements):
            split_blocks[block] = (lcs, lcs_idxs[0])

        graph_sim = graph_sim[len(lcs):]

    return orig_blocks, split_blocks


#
# Simple Optimizations
#

def remove_redundant_jumps(graph: nx.DiGraph):
    change = False
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
                last_statement = pred.statements[-1]
                pred.statements[-1] = correct_jump_targets(
                    last_statement,
                    {block.addr: succ.addr}
                )

                graph.add_edge(pred, succ)
            break

        if not remove_queue:
            break

        print(f"REMOVING IN SIMPLE_REDUNDANT_JUMP: {remove_queue}")
        graph.remove_nodes_from(remove_queue)
        change |= True

    return graph, change




#
# Target Construction
#

class MergeTarget:
    def __init__(self,
                 predecessor_map: Dict[Block, List[Block]],
                 pre_block_map: Dict[Block, Block],
                 post_block_map: Dict[Block, Block],
                 successor_map: Dict[Block, List[Block]],
                 original_graph: nx.DiGraph
                 ):
        # [start_block, predecessor]
        self.predecessor_map = predecessor_map
        # [orig_block, pre_block]
        self.pre_block_map = pre_block_map
        # [end_block, post_block]
        self.post_block_map = post_block_map
        # [end_block, successor]
        self.successor_map = successor_map
        self.original_graph = original_graph

    def __str__(self):
        return f"<MergeTarget: {{\npreds[{self.predecessor_map}],\npre_blocks[{self.pre_block_map}],\n" \
               f"post_blocks[{self.post_block_map}],\nsuccs[{self.successor_map}]\n}}"

    def __repr__(self):
        return str(self)


def generate_merge_targets(blocks, graph: nx.DiGraph) -> Tuple[nx.DiGraph, Dict[Block, MergeTarget]]:
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
    graph_lcs = longest_ail_graph_subseq(blocks, graph)

    # collect original graphs with their starts and ends
    merge_base = blocks[0]
    merge_graph = None

    for block in blocks:
        orig_blocks, split_blocks = ail_similarity_to_orig_blocks(block, graph_lcs, graph)
        removable_graph: nx.DiGraph = nx.subgraph(graph, orig_blocks)

        og_to_split = {}
        for og_block, split_info in split_blocks.items():
            lcs, idx = split_info
            og_to_split[og_block] = split_ail_block(og_block, idx, len(lcs))

        # create a merge_graph on first iteration (will always execute once)
        if block is merge_base and not merge_graph:
            base_og_to_merge = {
                og: split[1]
                for og, split in og_to_split.items() if split[1] is not None
            }

            merge_graph = clone_graph_with_splits(removable_graph.copy(), base_og_to_merge)
            merge_start = [node for node in merge_graph.nodes if merge_graph.in_degree(node) == 0][0]
            merge_ends = [node for node in merge_graph.nodes if merge_graph.out_degree(node) == 0]
            #breakpoint()
            merge_blocks, og_blocks = bfs_list_blocks(merge_start, merge_graph), bfs_list_blocks(merge_base, removable_graph)

            base_to_merge_end = {
                og: merge_end for og, merge_end in zip(og_blocks, merge_blocks)
                if merge_end in merge_ends
            }

        # create merge start association
        pred_map = {
            (split[0] if split[0] else block): list(graph.predecessors(block))
            for _, split in og_to_split.items()
        }
        if not pred_map:
            pred_map = {block: list(graph.predecessors(block))}

        pre_block_map = {
            (split[0] if split[0] else block): block
            for _, split in og_to_split.items()
        }
        if not pre_block_map:
            pre_block_map = {block: block}

        # create merge end association
        merge_end_to_og = {}
        block_pairs = ail_graph_similarity(block, merge_base, graph, only_blocks=True) \
            if block is not merge_base else [(og, og) for og, _ in base_to_merge_end.items()]
        for target_b, base_b in block_pairs:
            try:
                merge_end = base_to_merge_end[base_b]
            except KeyError:
                continue

            merge_end_to_og[merge_end] = target_b

        post_block_map = {
            merge_end: og_to_split[og][2] for merge_end, og in merge_end_to_og.items()
            if og in og_to_split and og_to_split[og][2]
        }
        succ_map = {
            merge_end: list(graph.successors(og)) for merge_end, og in merge_end_to_og.items()
        }
        merge_targets[block] = MergeTarget(
            pred_map,
            pre_block_map,
            post_block_map,
            succ_map,
            removable_graph
        )

    return merge_graph, merge_targets


class BlockMerger(OptimizationPass):
    """
    Merges blocks
    """

    ARCHES = ["X86", "AMD64", "ARMCortexM", "ARMHF", "ARMEL", ]
    PLATFORMS = ["cgc", "linux"]
    STAGE = OptimizationPassStage.DURING_REGION_IDENTIFICATION
    NAME = "Block Merger"
    DESCRIPTION = __doc__.strip()

    def __init__(self, func, region_identifier=None, reaching_definitions=None, **kwargs):
        self.region_identifier = region_identifier
        self.rd = reaching_definitions
        super().__init__(func, **kwargs)

        self.analyze()

    def _check(self):
        return True, {}

    #
    # Main Optimization Pass (after search)
    #

    def _analyze(self, cache=None):
        """
        Entry analysis routine that will trigger the other analysis stages
        """
        max_iters = 10
        curr_iter = 0

        self.exclusion_blocks = set()
        self.write_graph = self.simple_optimize_graph(self._graph)
        #self.out_graph = self.write_graph

        while True:
            curr_iter += 1
            print(f"=========================== RUNNING ANALYSIS ROUND {curr_iter} ===========================")
            if curr_iter >= max_iters:
                raise Exception("Exceeded max iterations allowed for duplication fixing")

            # do all writes on write_graph and all reads on read_graph
            self.read_graph = self.write_graph.copy()

            #
            # 0: Find candidates with duplicated AIL statements
            #

            candidates = self._find_initial_candidates()
            if not candidates:
                print("There are no duplicate statements in this function")
                break

            candidates = self._filter_candidates(candidates)
            if not candidates:
                print("There are no duplicate blocks in this function")
                break

            candidates = sorted(candidates, key=lambda x: len(x))
            print(f"CANDIDATES FOUND: {candidates}")
            candidate = candidates.pop()
            print(f"CANDIDATE SELECTED: {candidate}")

            #
            # 1: locate the longest duplicate sequence in a graph and split it at the merge
            #

            merge_graph, merge_targets = generate_merge_targets(candidate, self.read_graph)
            # any node in each target's original graph is removable
            removable_nodes = set(itertools.chain.from_iterable(
                [list(mt.original_graph.nodes) for _, mt in merge_targets.items()]
            ))
            merge_start = [node for node in merge_graph.nodes if merge_graph.in_degree(node) == 0][0]
            merge_ends = [node for node in merge_graph.nodes if merge_graph.out_degree(node) == 0]

            #
            # 2: destroy the old blocks that will be merged and add the new merge graph
            #

            print(f"DESTROYING NODES: {removable_nodes}")
            self.write_graph.remove_nodes_from(removable_nodes)
            self.write_graph = nx.compose(self.write_graph, merge_graph)

            #
            # 3: clone the conditional graph
            #

            merge_end_to_cond_graph = {}
            common_node_addr = shared_common_conditional_dom(candidate, self.read_graph).statements[-1].tags['ins_addr']
            # guarantees at least a single run
            for i, merge_end in enumerate(merge_ends):

                # merge ends with no post blocks need no graph
                if all(merge_end not in trgt.post_block_map for _, trgt in merge_targets.items()):
                    continue

                #breakpoint()
                cond_graph, pre_graph_map = self.copy_cond_graph(candidate, self.read_graph, idx=i + 1*curr_iter)
                try:
                    root_cond = [node for node in cond_graph.nodes if cond_graph.in_degree(node) == 0][0]
                except IndexError:
                    print("This duplication is in a looping condition, using a node estimate")
                    root_cond = find_block_by_addr(cond_graph, common_node_addr)

                merge_end_to_cond_graph[merge_end] = (root_cond, cond_graph)

            #
            # 4: replace the edges from the preds to the pre block
            #

            for _, merge_target in merge_targets.items():
                for pre_blk, old_blk in merge_target.pre_block_map.items():
                    new_block = pre_blk if pre_blk != old_blk else merge_start
                    for pred in merge_target.predecessor_map[pre_blk]:
                        last_statement = pred.statements[-1]
                        pred.statements[-1] = correct_jump_targets(
                            last_statement,
                            {old_blk.addr: new_block.addr},
                        )

                        self.write_graph.add_edge(pred, new_block)

                    if new_block == pre_blk:
                        self.write_graph.add_edge(pre_blk, merge_start)
            #
            # 5: make the merge graph ends point to conditional graph copies
            #

            for merge_end, cond_graph_info in merge_end_to_cond_graph.items():
                cond_root, cond_graph = cond_graph_info
                self.exclusion_blocks.update({blk for blk in cond_graph.nodes})
                self.write_graph = nx.compose(self.write_graph, cond_graph)
                self.write_graph.add_edge(merge_end, cond_root)

            #
            # 6: make the new conditionals point to the post-block
            #

            for merge_end, cond_graph_info in merge_end_to_cond_graph.items():
                cond_root, cond_graph = cond_graph_info

                for block, merge_target in merge_targets.items():
                    try:
                        new_block = merge_target.post_block_map[merge_end]
                    except KeyError:
                        new_block = merge_target.successor_map[merge_end][0] \
                            if len(merge_target.successor_map[merge_end]) > 0 else None

                    # skip conditionals that actually have no continuation
                    if not new_block:
                        continue

                    for cond in cond_graph.nodes:
                        last_stmt = cond.statements[-1]
                        cond.statements[-1] = correct_jump_targets(
                            last_stmt,
                            {block.addr: new_block.addr}
                        )

                        if (isinstance(last_stmt, ConditionalJump) and new_block.addr in (last_stmt.true_target.value, last_stmt.false_target.value))\
                                or (isinstance(last_stmt, Jump) and new_block.addr == last_stmt.target.value):
                            self.write_graph.add_edge(cond, new_block)
            #
            # 7: make the post blocks continue to the next successors
            #

            for _, merge_target in merge_targets.items():
                for merge_end, post_block in merge_target.post_block_map.items():
                    if not post_block:
                        continue

                    for suc in merge_target.successor_map[merge_end]:
                        self.write_graph.add_edge(post_block, suc)
            #
            # 8: AD-HOC-FIX nodes that could've been modified (fixed point)
            #

            while True:
                new_nodes = []
                for node in merge_graph.nodes:
                    new_nodes += list(self.write_graph.predecessors(node))
                    new_nodes += list(self.write_graph.successors(node))
                    new_nodes += [node]
                modified_nodes = set(new_nodes)

                for node in modified_nodes:
                    updated = False
                    # only attempt to fix nodes that end in a jump
                    last_stmt = node.statements[-1]
                    if isinstance(last_stmt, ConditionalJump):
                        targets = [last_stmt.true_target.value, last_stmt.false_target.value]
                    elif isinstance(last_stmt, Jump):
                        targets = [last_stmt.target.value]
                    else:
                        continue

                    # check if the jump targets of each node are present in all successors of node
                    all_succ = [suc.addr for suc in self.write_graph.successors(node)]
                    for value in targets:
                        if value in all_succ:
                            continue

                        # if not, find that block, re-add it
                        try:
                            new_succ = find_block_by_addr(self.write_graph, value)
                        except Exception:
                            continue

                        self.write_graph.add_edge(node, new_succ)
                        updated = True
                        break

                    if updated:
                        break

                else:
                    break

            self.write_graph = self.simple_optimize_graph(self.write_graph)

        #breakpoint()
        self.out_graph = self.write_graph #self.remove_simple_similar_blocks(self.write_graph)

    #
    # Search Stages
    #

    def copy_cond_graph(self, merge_start_nodes, graph, idx=1):
        # [merge_node, nx.DiGraph: pre_graph]
        pre_graphs_maps = {}
        # [merge_node, nx.DiGraph: full_graph]
        graph_maps = {}
        # [merge_node, removed_nodes]
        removed_node_map = defaultdict(list)

        # create a subgraph for every merge_start and the dom
        shared_conditional_dom = shared_common_conditional_dom(merge_start_nodes, graph)
        for merge_start in merge_start_nodes:
            paths_between = nx.all_simple_paths(graph, source=shared_conditional_dom, target=merge_start)
            nodes_between = {node for path in paths_between for node in path}
            graph_maps[merge_start] = nx.subgraph(graph, nodes_between)

        # create remove nodes for nodes that are shared among all graphs (conditional nodes)
        for block0, graph0 in graph_maps.items():
            for node in graph0.nodes:
                for block1, graph1 in graph_maps.items():
                    if block0 == block1:
                        continue

                    if node in graph1.nodes:
                        removed_node_map[block0].append(node)

        # make the pre-graph from removing the nodes
        for block, blocks_graph in graph_maps.items():
            pre_graph = blocks_graph.copy()
            pre_graph.remove_nodes_from(removed_node_map[block])
            pre_graphs_maps[block] = pre_graph

        # make a conditional graph from any remove_nodes map (no deepcopy)
        temp_cond_graph: nx.DiGraph = nx.subgraph(graph, removed_node_map[merge_start_nodes[0]])

        # deep copy the graph and remove instructions that are not control flow altering
        cond_graph = nx.DiGraph()

        block_to_insn_map = {
            node.addr: node.statements[-1].tags['ins_addr'] for node in temp_cond_graph.nodes()
        }
        for merge_start in merge_start_nodes:
            for node in pre_graphs_maps[merge_start].nodes:
                block_to_insn_map[node.addr] = merge_start.addr

        # fix nodes that don't end in a jump
        for node in temp_cond_graph:
            successors = list(temp_cond_graph.successors(node))
            if not isinstance(node.statements[-1], (ConditionalJump, Jump)) and len(successors) == 1:
                node.statements += [Jump(None, Const(None, None, successors[0].addr, self.project.arch.bits), ins_addr=successors[0].addr)]

        # deepcopy every node in the conditional graph with a unique address
        crafted_blocks = {}
        for edge in temp_cond_graph.edges:
            new_edge = ()
            for block in edge:
                last_stmt = block.statements[-1]

                try:
                    new_block = crafted_blocks[block.addr]
                except KeyError:
                    new_block = ail_block_from_stmts([deepcopy_ail_anyjump(last_stmt, idx=idx)])
                    crafted_blocks[block.addr] = new_block

                new_edge += (new_block,)
            cond_graph.add_edge(*new_edge)

        # graphs with no edges but only nodes
        if len(list(cond_graph.nodes)) == 0:
            for node in temp_cond_graph.nodes:
                last_stmt = node.statements[-1]
                cond_graph.add_node(ail_block_from_stmts([deepcopy_ail_anyjump(last_stmt, idx=idx)]))

        # correct every jump target
        for node in cond_graph.nodes:
            node.statements[-1] = correct_jump_targets(
                node.statements[-1],
                block_to_insn_map
            )

        return cond_graph, pre_graphs_maps

    @property
    def _block_only_regions(self):
        work_list = [self.region_identifier.region]
        block_only_regions = []
        seen_regions = set()
        while work_list:
            children_regions = []
            for region in work_list:
                children_blocks = []
                for node in region.graph.nodes:
                    if isinstance(node, Block):
                        children_blocks.append(node.addr)
                    elif isinstance(node, MultiNode):
                        children_blocks += [n.addr for n in node.nodes]
                    elif isinstance(node, GraphRegion):
                        if node not in seen_regions:
                            children_regions.append(node)
                            children_blocks.append(node.head.addr)
                            seen_regions.add(node)
                    else:
                        continue

                if children_blocks:
                    block_only_regions.append(children_blocks)

            work_list = children_regions

        return block_only_regions

    def _share_subregion(self, blocks: List[Block]) -> bool:
        for region in self._block_only_regions:
            if all(block.addr in region for block in blocks):
                break
        else:
            return False

        return True

    def _find_initial_candidates(self) -> List[Tuple[Block, Block]]:
        initial_candidates = list()
        for b0, b1 in combinations(self.read_graph.nodes, 2):
            # TODO: find a better fix for this! Some duplicated nodes need destruction!
            # skip purposefully duplicated nodes
            if any(isinstance(b.idx, int) and b.idx > 0 for b in [b0, b1]):
                continue

            # blocks must share a region
            if not self._share_subregion([b0, b1]):
                continue

            # must share a common dominator
            if not shared_common_conditional_dom([b0, b1], self.read_graph):
                continue

            # special case: when we only have a single stmt
            if len(b0.statements) == len(b1.statements) == 1:
                try:
                    is_similar = similar(b0, b1, graph=self.read_graph)
                except Exception:
                    continue

                if is_similar:
                    initial_candidates.append((b0, b1))
                    continue

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
                    # XXX: used to be just likes()
                    if similar(stmt0, stmt1, self.read_graph):
                        stmt_in_common = True
                        break

                if stmt_in_common:
                    pair = (b0, b1)
                    # only append pairs that share a dominator
                    if shared_common_conditional_dom(pair, self.read_graph) is not None:
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

        blk_descendants = {
            (b0, b1): set(nx.descendants(self.read_graph, b0)).union(
                set(nx.descendants(self.read_graph, b1)).union({b0, b1})
            )
            for b0, b1 in candidates
        }

        while True:
            removal_queue = list()
            for candidate in candidates:
                if candidate in removal_queue:
                    continue

                stop = False
                for candidate2 in candidates:
                    if candidate2 == candidate or candidate2 not in blk_descendants:
                        continue

                    descendants = blk_descendants[candidate2]
                    if all(c in descendants for c in candidate):
                        removal_queue.append(candidate)
                        del blk_descendants[candidate]
                        stop = True
                        break

                if stop:
                    break

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

                for can1 in candidates:
                    if can0 == can1 or can1 in queued:
                        continue

                    # only try a merge if candidates share a node in common
                    if not set(can0).intersection(set(can1)):
                        continue

                    lcs, _ = longest_ail_subseq([b.statements for b in set(can0 + can1)])
                    if not lcs:
                        continue

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
        candidates = [
            tuple(sorted(candidate, key=lambda x: x.addr)) for candidate in candidates
        ]
        candidates = sorted(candidates, key=lambda x: sum([c.addr for c in x]))

        return candidates

    #
    # Simple Optimizations (for cleanup)
    #

    def remove_simple_similar_blocks(self, graph: nx.DiGraph):
        """
        Removes blocks that have all statements that are similar and the same successors
        @param graph:
        @return:
        """
        change = False
        not_fixed = True
        while not_fixed:
            not_fixed = False
            nodes = list(graph.nodes())
            remove_queue = list()

            for b0, b1 in itertools.combinations(nodes, 2):
                if not self._share_subregion([b0, b1]):
                    continue

                b0_suc, b1_suc = set(graph.successors(b0)), set(graph.successors(b1))

                # blocks should have the same successors
                if b0_suc != b1_suc:
                    continue

                # special case: when we only have a single stmt
                if len(b0.statements) == len(b1.statements) == 1:
                    try:
                        is_similar = similar(b0, b1, graph=graph)
                    except Exception:
                        continue

                    if not is_similar:
                        continue

                elif not b0.likes(b1):
                    continue

                remove_queue.append((b0, b1))
                break

            if not remove_queue:
                break

            print(f"REMOVING IN SIMPLE_DUP: {remove_queue}")
            for b0, b1 in remove_queue:
                if not (graph.has_node(b0) or graph.has_node(b1)):
                    continue

                for suc in graph.successors(b1):
                    graph.add_edge(b0, suc)

                for pred in graph.predecessors(b1):
                    last_statement = pred.statements[-1]
                    pred.statements[-1] = correct_jump_targets(
                        last_statement,
                        {b1.addr: b0.addr}
                    )
                    graph.add_edge(pred, b0)

                graph.remove_node(b1)
                not_fixed = True
                change |= True

        return graph, change

    def simple_optimize_graph(self, graph):
        def _to_ail_supergraph(graph_):
            # make supergraph conversion always say no change
            return to_ail_supergraph(graph_), False

        new_graph = graph.copy()
        opts = [
            _to_ail_supergraph,
            remove_redundant_jumps,
        ]

        change = True
        while change:
            change = False
            for opt in opts:
                new_graph, has_changed = opt(new_graph)
                change |= has_changed

        return new_graph


AnalysesHub.register_default("BlockMerger", BlockMerger)