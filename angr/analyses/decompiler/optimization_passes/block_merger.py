from typing import List, Tuple, Optional, Dict
import logging
import copy
from itertools import combinations
import itertools

import networkx
import networkx as nx

from ailment.block import Block
from ailment.statement import Statement, ConditionalJump, Jump
from ailment.expression import Const

from ... import AnalysesHub
from .optimization_pass import OptimizationPass, OptimizationPassStage
from ..utils import to_ail_supergraph
from ....utils.graph import dominates


_l = logging.getLogger(name=__name__)


#
# Utils
#

import toml
def update_toml(toml_path, update_dict):
    with open(toml_path, "r") as fp:
        data = toml.load(fp)
    data.update(update_dict)
    with open(toml_path, "w") as fp:
        toml.dump(data, fp)

def graph_block_by_addr(graph: networkx.DiGraph, addr, insn_addr=False):
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


def similar(ail_obj1, ail_obj2, graph: nx.DiGraph = None):
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
                t1_blk, t2_blk = graph_block_by_addr(graph, t1), graph_block_by_addr(graph, t2)
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


def kmp_search_ail_stmt(search_pattern, stmt_seq, graph=None):
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
        while shift <= pos and not similar(search_pattern[pos], search_pattern[pos - shift], graph=graph):
            shift += shifts[pos - shift]
        shifts[pos + 1] = shift

    # do the actual search
    start_pos = 0
    match_len = 0
    for c in stmt_seq:
        while match_len == len(search_pattern) or match_len >= 0 and \
                not similar(search_pattern[match_len], c, graph=graph):
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


def deepcopy_ail_condjump(stmt: ConditionalJump):
    true_target: Const = stmt.true_target
    false_target: Const = stmt.false_target
    tags = stmt.tags.copy()

    return ConditionalJump(
        1,
        stmt.condition.copy(),
        Const(1, true_target.variable, true_target.value, true_target.bits, **true_target.tags.copy()),
        Const(1, false_target.variable, false_target.value, false_target.bits, **false_target.tags.copy()),
        **tags
    )


def share_common_ail_stmt(nodes):
    shared = []
    first_pass = True
    for b0, b1 in combinations(nodes, 2):
        # find all sharing statements
        block_share = []
        for stmt1 in b0.statements:
            for stmt2 in b1.statements:
                if similar(stmt1, stmt2):
                    block_share.append(stmt1)
                    break

        # if not first pass, filter out any shared statements no in the blocks
        new_shared = []
        if first_pass:
            new_shared = block_share
        else:
            for stmt in block_share:
                for old_stmt in shared:
                    if similar(stmt, old_stmt):
                        new_shared.append(old_stmt)
                        break

        shared = new_shared
    _l.info(f"COMMON STATEMENTS: {shared}")
    return len(shared) > 0


def lcs_ail_stmts(blocks, graph=None):
    # generate the lcs for each pair
    lcs_list = list()
    for b0, b1 in combinations(blocks, 2):
        stmts0, stmts1 = b0.statements, b1.statements
        stmt_seqs = sub_lists(stmts0)
        matches = [(stmt_seq, list(kmp_search_ail_stmt(stmt_seq, stmts1, graph=graph))) for stmt_seq in stmt_seqs]
        match_seq, match_pos_in_1 = max(matches, key=lambda m: len(m[0]) if len(m[1]) > 0 else -1)
        lcs_list.append(match_seq)

    # take each pairs lcs and find the lcs of those lcs (to get the overall lcs)
    _l.info(f"LCS LIST: {lcs_list}")
    not_fixed = True
    while not_fixed:
        not_fixed = False
        common_lcs = list()

        # stop once we only have one
        if len(lcs_list) == 1:
            break

        # check each lcs against the others in the list
        for lcs in lcs_list:
            if all(True if len(list(kmp_search_ail_stmt(lcs, other_lcs, graph=graph))) > 0 else False for other_lcs in lcs_list):
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
    lcs = lcs_list[0]

    block_idxs = {}
    for block in blocks:
        block_idxs[block] = list(kmp_search_ail_stmt(lcs, block.statements, graph=graph))[0]

    return lcs, block_idxs


def similar_graph_blocks(start_blk0: Block, start_blk1: Block, graph: nx.DiGraph):
    """
    Takes the start blocks of two sub-graphs that reside in graph. It returns a list of blocks that are similar
    in the subgraphs. The tuple will provide the blocks that are similar in both graphs.

    Theory on Algorithm:
    If we want to find how two graphs compare we just need to iterate both graphs nodes in the same order. When
    we come to a ConditionalJump, we just align the search by using the true and false targets. The graph can start
    with the first block being different in start statements, but all blocks after it must be exact copies.

    @rtype: List[ Tuple[ List[Statement], Tuple[Block, int], Tuple[Block, int] ] ]
    @return: A list of tuples (lcs, (blk0, blk0_idx), (blk1, blk1_idx))
    """
    blocks = [start_blk0, start_blk1]
    lcs, block_idxs = lcs_ail_stmts(blocks, graph=graph)
    lcs_len = len(lcs)
    block_splits = [(lcs, (start_blk0, block_idxs[blocks[0]]), (start_blk1, block_idxs[blocks[1]]))]

    # check if both blocks end in the same statements
    if not all(lcs_len + block_idxs[block] == len(block.statements) for block in blocks):
        return block_splits

    # it's an actual graph, do the search
    successors = {
        start_blk0: list(graph.successors(start_blk0)),
        start_blk1: list(graph.successors(start_blk1))
    }

    if len(successors[start_blk0]) == len(successors[start_blk1]) == 1:
        # check how the successors differ
        return block_splits + similar_graph_blocks(successors[start_blk0][0], successors[start_blk1][0], graph)
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
        return block_splits + \
            similar_graph_blocks(targets[start_blk0]["true"], targets[start_blk1]["true"], graph) + \
            similar_graph_blocks(targets[start_blk0]["false"], targets[start_blk1]["false"], graph)

    # if none of the successors amt match, we end the search here
    return block_splits


def lcs_ail_graph_blocks(start_blocks: List[Block], graph: nx.DiGraph) -> Tuple[nx.DiGraph, Dict, List[Block]]:
    # TODO: support more than a 2 graph search
    if len(start_blocks) > 2:
        raise Exception("CANT DO AIL GRAPH MERGING FOR MORE THAN 2 BLOCKS")

    # this should only be one iteration right now
    for blk0, blk1 in combinations(start_blocks, 2):
        merge_blocks = []
        split_blocks = {}
        removable_nodes = []

        #  [ ( lcs, (blk0, blk0_idx), (blk1, blk1_idx) ) , ...]
        block_diffs = similar_graph_blocks(blk0, blk1, graph)
        #breakpoint()

        # find all the blocks ready for merging
        for lcs, diff0, diff1 in block_diffs:
            lcs_len = len(lcs)
            # if either block has some split record it
            if (len(diff0[0].statements) != lcs_len + diff0[1]) or (len(diff1[0].statements) != lcs_len + diff1[1]):
                for block, block_idx in (diff0, diff1):
                    if len(block.statements) != lcs_len + block_idx:
                        pre_split = ail_block_from_stmts(block.statements[:block_idx])
                        merge_split = ail_block_from_stmts(block.statements[block_idx:block_idx+lcs_len])
                        post_split = ail_block_from_stmts(block.statements[block_idx+lcs_len:])
                        split_blocks[block] = (pre_split, merge_split, post_split)

            # if no split, it's ready for merging
            else:
                # add any block for merging
                merge_blocks.append(diff0[0])
                removable_nodes += [diff0[0], diff1[0]]

        merge_graph = nx.subgraph(graph, merge_blocks)

        # fix the splits
        # TODO: finish this
        fixed = set()
        for block, pre, merge, post in split_blocks:
            if merge not in fixed:
                pass




        # (graph, [(pre_split, merge_split, post_split), ...]
        return merge_graph, split_blocks, removable_nodes


class MergeTarget:
    def __init__(self, predecessor_map: Dict[Block, List[Block]], pre_block_map: Dict[Block, Block],
                 post_block_map: Dict[Block, Block], successor_map: Dict[Block, List[Block]]
                 ):
        # [start_block, predecessor]
        self.predecessor_map = predecessor_map
        # [orig_block, new_block]
        self.pre_block_map = pre_block_map
        # [orig_block, new_block]
        self.post_block_map = post_block_map
        # [end_block, successor]
        self.successor_map = successor_map



#
# Merger Optimization
#


def remove_graph_single_gotos(graph: nx.DiGraph):
    remove_queue = list()
    for block in graph.nodes:
        if len(block.statements) != 1:
            continue

        stmt = block.statements[0]
        if not isinstance(stmt, Jump):
            continue

        # confirmed we want to remove this
        succ = list(graph.successors(block))
        if len(succ) <= 0:
            continue

        succ = succ[0]
        remove_queue.append(block)
        for pred in graph.predecessors(block):
            if isinstance(pred.statements[-1], ConditionalJump):
                if_stmt = pred.statements[-1]
                if if_stmt.true_target.value == block.addr:
                    if_stmt.true_target.value = succ.addr
                else:
                    if_stmt.false_target.value = succ.addr

            graph.add_edge(pred, succ)

    graph.remove_nodes_from(remove_queue)
    return graph


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

    def _shares_common_dom(self, nodes):
        entry_blk = [node for node in self.copy_graph.nodes if self.copy_graph.in_degree(node) == 0][0]
        idoms = nx.algorithms.immediate_dominators(self.copy_graph, entry_blk)
        dominators = [idoms[node] for node in nodes]

        for dom in dominators:
            if all(dominates(idoms, dom, node) for node in nodes):
                return True

        return False

    def _copy_cond_graph(self, end_cond_nodes):
        # special case: the graph is actually just a single node
        if len(end_cond_nodes) == 1:
            new_cond_graph = nx.DiGraph()
            new_cond_graph.add_node(ail_block_from_stmts([deepcopy_ail_condjump(end_cond_nodes[0].statements[-1])]))
            return new_cond_graph

        entry_blk = [node for node in self.copy_graph.nodes if self.copy_graph.in_degree(node) == 0][0]
        idoms = nx.algorithms.immediate_dominators(self.copy_graph, entry_blk)
        end_idoms = [idoms[end_node] for end_node in end_cond_nodes]

        # make a subgraph that includes every ending conditional node and all the idoms
        cond_graph = nx.subgraph(self.copy_graph, end_idoms+end_cond_nodes)

        # in the new graph we will make old addrs +1
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
            new_cond_graph.add_node(ail_block_from_stmts([deepcopy_ail_condjump(node.statements[-1])]))

        # second pass: correct all the old edges
        for node in new_cond_graph.nodes():
            if_stmt = node.statements[-1]

            # make new edges
            old_sucs = orig_successors_by_insn[node.addr]
            old_node = orig_nodes_by_insn[node.addr]
            old_true = old_node.statements[-1].true_target.value
            old_false = old_node.statements[-1].false_target.value
            for old_suc in old_sucs:
                new_suc = graph_block_by_addr(new_cond_graph, old_suc.statements[-1].tags['ins_addr'])

                # correct the conditional
                if old_true == old_suc.addr:
                    if_stmt.true_target.value = new_suc.addr
                elif old_false == old_suc.addr:
                    if_stmt.false_target.value = new_suc.addr

                # add the edge
                new_cond_graph.add_edge(node, new_suc)

        return new_cond_graph

    #
    # Analysis stages
    #

    def _fast_find_initial_candidates(self) -> List[Tuple[Block, Block]]:
        init_candidates = []
        for node in self.copy_graph.nodes():
            if not isinstance(node.statements[-1], ConditionalJump):
                continue

            b0, b1 = list(self.copy_graph.successors(node))[:]
            should_break = False
            for stmt1 in b0.statements:
                for stmt2 in b1.statements:
                    if stmt1.likes(stmt2):
                        init_candidates.append((b0, b1))
                        should_break = True
                        break

                # after finding a match in this block, we should leave it
                if should_break:
                    break

        return init_candidates

    def _filter_candidates(self, candidates):
        """
        Preform a series of filters on the candidates to reduce the fast set to an assured set of
        the duplication case we are searching for.
        """
        # filter down candidates
        filtered_candidates = []
        for candidate in candidates:
            if not self._shares_common_dom(candidate):
                continue

            filtered_candidates.append(candidate)

        # XXX: REMOVE ME AFTER EVAL
        #
        #
        status = {
            "success": True,
            "duplicate_pairs": 0,
            "duplicate_locations": []
        }
        for b0, b1 in filtered_candidates:
            status["duplicate_locations"].append((b0.addr, b1.addr))
        status["duplicate_pairs"] = len(filtered_candidates)
        name = self._func.name if self._func.name else hex(self._func.addr)
        update_toml(f"{self.project.filename}.toml", {name: status})
        return


        # merge candidates
        not_fixed = True
        _l.info(f"filtered starting: {filtered_candidates}")
        while not_fixed:
            not_fixed = False
            queued = set()
            merged_candidates = []

            # no merging needs to be done, there is only one candidate left
            if len(filtered_candidates) == 1:
                break

            for can0 in filtered_candidates:
                # skip candidates being merged
                if can0 in queued:
                    continue

                # make sure we dont try to merge a singleton
                queued.add(can0)
                for blk in can0:
                    for can1 in filtered_candidates:
                        if can1 in queued:
                            continue

                        # merge and queue
                        if blk in can1 and share_common_ail_stmt(can0 + can1):
                            merged_candidates.append(tuple(set(can0 + can1)))
                            queued.add(can1)
                            not_fixed |= True
                            break

            filtered_candidates = merged_candidates + [node for node in filtered_candidates if node not in queued]
            _l.info(f"filtered now: {filtered_candidates}")

        return filtered_candidates

    def generate_merge_targets(self, blocks, graph: nx.DiGraph) -> Tuple[nx.DiGraph, Dict[Block, MergeTarget], List[Block]]:
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
        @return:
        """
        merge_targets = {}

        # find the longest sequence in the potential heads of the graph
        lcs, block_idxs = lcs_ail_stmts(blocks, graph=graph)
        lcs_len = len(lcs)

        # special case: if the longest common sequence does not end each block (single block graph)
        # TODO: change the >2 part
        if not all(lcs_len + block_idxs[block] == len(block.statements) for block in blocks) or len(blocks) > 2:
            merge_graph = nx.DiGraph()
            merge_graph.add_node(ail_block_from_stmts(lcs))
            for block in blocks:
                dup_idx = block_idxs[block]
                predecessor_map = {block: list(graph.predecessors(block))}
                pre_block_map = {block: ail_block_from_stmts(block.statements[dup_idx:dup_idx+lcs_len])}
                post_block_map = {block: ail_block_from_stmts(block.statements[dup_idx+lcs_len:])}
                successor_map = {block: list(graph.successors(block))}
                merge_targets[block] = MergeTarget(predecessor_map, pre_block_map, post_block_map, successor_map)

            return merge_graph, merge_targets, blocks

        # not a single block, but an entire graph, need to find lcs of graph
        merge_graph, split_blocks, removable_nodes = lcs_ail_graph_blocks(blocks, graph)
        start_block = [node for node in merge_graph.nodes if merge_graph.in_degree(node) == 0][0]
        end_blocks = [node for node in merge_graph.nodes if merge_graph.out_degree(node) == 0]

        # XXX: complete bonkers code
        successor_map = {}
        predecessor_map = {start_block: list(graph.predecessors(start_block))}
        for block in end_blocks:
            successor_map[block] = list(graph.successors(block))
            merge_targets[block] = MergeTarget(predecessor_map, {}, {}, successor_map)

        return merge_graph, merge_targets, removable_nodes


    def _analyze(self, cache=None):
        """
        Entry analysis routine that will trigger the other analysis stages
        """
        # do all writes on out_graph and all reads on copy_graph
        self.out_graph = remove_graph_single_gotos(to_ail_supergraph(self._graph))
        self.copy_graph = self.out_graph.copy()

        candidates = self._fast_find_initial_candidates()
        if not candidates:
            status = {
                "success": True,
                "duplicate_pairs": 0,
                "duplicate_locations": []
            }
            name = self._func.name if self._func.name else hex(self._func.addr)
            update_toml(f"{self.project.filename}.toml", {name: status})
            _l.info("There are no duplicate statements in this function")
            return

        candidates = self._filter_candidates(candidates)
        return
        if not candidates:
            _l.info("There are no duplicate blocks in this function")
            return

        _l.info(f"CANDIDATES FOUND: {candidates}")

        for blocks in candidates:
            # 1: locate the longest duplicate stmt sequence in blocks and split them
            merge_graph, merge_targets, removable_nodes = self.generate_merge_targets(blocks, self.copy_graph)
            merge_start = [node for node in merge_graph.nodes if merge_graph.in_degree(node) == 0][0]
            merge_ends = [node for node in merge_graph.nodes if merge_graph.out_degree(node) == 0]

            # 2: destroy the old blocks that will be merged
            self.out_graph.remove_nodes_from(removable_nodes + [b for b in blocks])
            # any merge block will do, they are all the same
            self.out_graph.add_node(merge_start)

            # 3: clone the conditional graph
            # TODO: bad hack
            merge_target_preds = [trgt.predecessor_map[merge_start] for block, trgt in merge_targets.items()]
            merge_target_preds = list(itertools.chain.from_iterable(merge_target_preds))
            cond_graph = self._copy_cond_graph(merge_target_preds)
            root_cond = [node for node in cond_graph.nodes if cond_graph.in_degree(node) == 0][0]

            # 4: replace the edges of the pre-blocks
            for pred in set(merge_target_preds):
                if not isinstance(pred.statements[-1], ConditionalJump):
                    continue

                if_stmt: ConditionalJump = pred.statements[-1]
                for suc in self.copy_graph.successors(pred):
                    # only need to update edges going to merge target blocks
                    if suc.addr not in merge_targets:
                        continue

                    merge_target = merge_targets[suc.addr]
                    new_block = merge_target.pre_block_map if merge_target.pre_block_map else merge_start
                    self.out_graph.add_edge(pred, new_block)

                    # update conditional target value
                    new_target = if_stmt.true_target if if_stmt.true_target.value == suc.addr else if_stmt.false_target
                    new_target.value = new_block.addr

            # 5: make the pre blocks point to the merge block
            for _, trgt in merge_targets.items():
                if trgt.pre_block_map:
                    for orig_b, new_b in trgt.pre_block_map.items():
                        self.out_graph.add_edge(new_b, merge_start)

            # 6: make the merge block point to the conditional root
            self.out_graph = nx.compose(self.out_graph, cond_graph)
            self.out_graph.add_edge(merge_start, root_cond)

            # 7: make the conditional point to the post-block
            for cond in cond_graph.nodes():
                if_stmt: ConditionalJump = cond.statements[-1]
                for attr in ["true_target", "false_target"]:
                    target = getattr(if_stmt, attr)

                    try:
                        target_blk = graph_block_by_addr(self.copy_graph, target.value)
                        merge_target: MergeTarget = merge_targets[target_blk]
                    except:
                        print(f"SKIPPING {attr} for {hex(cond.addr)}")
                        continue

                    if merge_target.post_block_map:
                        new_block_target = merge_target.post_block_map
                    else:
                        # TODO: fix this for multiple outgoing nodes of a merge
                        new_block_target = merge_target.successor_map[target_blk][0]

                    target.value = new_block_target.addr
                    self.out_graph.add_edge(cond, new_block_target)

            # 8: make the post blocks continue to the next successors
            for _, trgt in merge_targets.items():
                if trgt.post_block_map:
                    for orig_b, new_b in trgt.post_block_map.items():
                        for suc in self.copy_graph.successors(orig_b):
                            self.out_graph.add_edge(new_b, suc)

            # TODO: make this a fixed-point algorithm
            return


AnalysesHub.register_default("BlockMerger", BlockMerger)
