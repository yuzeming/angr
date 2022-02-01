from typing import List, Tuple, Optional, Dict
import logging
import copy
from itertools import combinations

import networkx as nx

from ailment.block import Block
from ailment.statement import Statement, ConditionalJump, Call, Jump

from ... import AnalysesHub
from .optimization_pass import OptimizationPass, OptimizationPassStage
from ..utils import to_ail_supergraph
from ....utils.graph import dominates


_l = logging.getLogger(name=__name__)


#
# Utils
#

def s2u(s, bits):
    if s > 0:
        return s
    return (1 << bits) + s


def sub_lists(seq):
    lists = [[]]
    for i in range(len(seq) + 1):
        for j in range(i):
            lists.append(seq[j: i])
    return lists


def pattern_in_seq(pattern, seq):
    """
    Uses the Knuth-Morris-Pratt algorithm for searching.
    Found: https://code.activestate.com/recipes/117214/.

    Returns a generator of positions, which will be empty if its not found.
    """
    # allow indexing into pattern and protect against change during yield
    pattern = list(pattern)

    # build table of shift amounts
    shifts = [1] * (len(pattern) + 1)
    shift = 1
    for pos in range(len(pattern)):
        while shift <= pos and not pattern[pos].likes(pattern[pos - shift]):
            shift += shifts[pos - shift]
        shifts[pos + 1] = shift

    # do the actual search
    start_pos = 0
    match_len = 0
    for c in seq:
        while match_len == len(pattern) or match_len >= 0 and not pattern[match_len].likes(c):
            start_pos += shifts[match_len]
            match_len -= shifts[match_len]
        match_len += 1
        if match_len == len(pattern):
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


class MergeTarget:
    def __init__(self, target, dup_idx, dup_len, graph: nx.DiGraph):
        self.target = target
        self._graph = graph

        self.target_addr = target.addr
        self.predecessors = list()
        self.pre_block: Block = None
        self.merge_block: Block = None
        self.post_block: Block = None
        self.successors = list()

        self._construct_blocks(dup_idx, dup_len)

    def _construct_blocks(self, dup_idx, dup_len):
        self.pre_block = ail_block_from_stmts(self.target.statements[:dup_idx])
        self.merge_block = ail_block_from_stmts(self.target.statements[dup_idx:dup_idx+dup_len])
        self.post_block = ail_block_from_stmts(self.target.statements[dup_idx+dup_len:])

        self.predecessors = list(self._graph.predecessors(self.target))
        self.successors = list(self._graph.successors(self.target))


#
# Merger Optimization
#

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

        """"
        pre1 = list(self.copy_graph.predecessors(node1))
        pre2 = list(self.copy_graph.predecessors(node2))
        ans1 = list(nx.algorithms.ancestors(self.copy_graph, node1))
        ans2 = list(nx.algorithms.ancestors(self.copy_graph, node2))

        return all([p1 in ans2 for p1 in pre1]) and all([p2 in ans1 for p2 in pre2])
        """
        return False

    def _share_common_stmt(self, nodes):
        shared = []
        first_pass = True
        for b0, b1 in combinations(nodes, 2):
            # find all sharing statements
            block_share = []
            for stmt1 in b0.statements:
                for stmt2 in b1.statements:
                    if stmt1.likes(stmt2):
                        block_share.append(stmt1)
                        break

            # if not first pass, filter out any shared statements no in the blocks
            new_shared = []
            if first_pass:
                new_shared = block_share
            else:
                for stmt in block_share:
                    for old_stmt in shared:
                        if stmt.likes(old_stmt):
                            new_shared.append(old_stmt)
                            break

            shared = new_shared
        print(f"COMMON STATEMENTS: {shared}")
        return len(shared) > 0

    def _longest_common_stmt_seq(self, blocks):
        # generate the lcs for each pair
        lcs_list = list()
        for b0, b1 in combinations(blocks, 2):
            stmts0, stmts1 = b0.statements, b1.statements
            stmt_seqs = sub_lists(stmts0)
            matches = [(stmt_seq, list(pattern_in_seq(stmt_seq, stmts1))) for stmt_seq in stmt_seqs]
            match_seq, match_pos_in_1 = max(matches, key=lambda m: len(m[0]) if len(m[1]) > 0 else -1)
            lcs_list.append(match_seq)

        # take each pairs lcs and find the lcs of those lcs (to get the overall lcs)
        print(f"LCS LIST: {lcs_list}")
        not_fixed = True
        while not_fixed:
            not_fixed = False
            common_lcs = list()

            # stop once we only have one
            if len(lcs_list) == 1:
                break

            # check each lcs against the others in the list
            for lcs in lcs_list:
                if all(True if len(list(pattern_in_seq(lcs, other_lcs))) > 0 else False for other_lcs in lcs_list):
                    # assure we are not readding the same lcs
                    for clcs in common_lcs:
                        if len(lcs) == len(clcs) and all(s1.likes(s2) for s1,s2 in zip(lcs, clcs)):
                            break
                    else:
                        common_lcs.append(lcs)
                        not_fixed |= True

            lcs_list = common_lcs
            print(f"LCS LIST ITERATION: {lcs_list}")

        # finally, locate the lcs in all blocks
        lcs = lcs_list[0]

        block_idxs = {}
        for block in blocks:
            block_idxs[block] = list(pattern_in_seq(lcs, block.statements))[0]

        return lcs, block_idxs

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

        TODO: need a way to group candidates that are more than a single pair, see if-else example
        """
        # filter down candidates
        filtered_candidates = []
        for candidate in candidates:
            if not self._shares_common_dom(candidate):
                continue

            filtered_candidates.append(candidate)

        # merge candidates
        not_fixed = True
        print(f"filtered starting: {filtered_candidates}")
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
                        if blk in can1 and self._share_common_stmt(can0 + can1):
                            merged_candidates.append(tuple(set(can0 + can1)))
                            queued.add(can1)
                            not_fixed |= True
                            break

            filtered_candidates = merged_candidates + [node for node in filtered_candidates if node not in queued]
            print(f"filtered now: {filtered_candidates}")

        return filtered_candidates

    def _analyze(self, cache=None):
        """
        Entry analysis routine that will trigger the other analysis stages
        """
        # do all writes on out_graph and all reads on copy_graph
        self.out_graph = to_ail_supergraph(self._graph)
        self.copy_graph = self.out_graph.copy()

        candidates = self._fast_find_initial_candidates()
        if not candidates:
            print("There are no duplicate statements in this function")
            return

        candidates = self._filter_candidates(candidates)
        if not candidates:
            print("There are no duplicate blocks in this function")
            return

        print(f"CANDIDATES FOUND: {candidates}")

        for blocks in candidates:
            # 1: locate the longest duplicate stmt sequence in blocks and split them
            lcs, block_idxs = self._longest_common_stmt_seq(blocks)
            lcs_len = len(lcs)
            merge_targets = {
                block.addr: MergeTarget(block, block_idxs[block], lcs_len, self.copy_graph)
                for block in blocks
            }

            # 2: destroy the old blocks that will be merged
            self.out_graph.remove_nodes_from(blocks)
            # any merge block will do, they are all the same
            merge_block = list(merge_targets.values())[0].merge_block
            self.out_graph.add_node(merge_block)

            # 3: replace the edges of the pre-blocks
            #breakpoint()
            # TODO: fill in the rest of the stuff I did below here!
            return







        for block0, block1 in candidates:
            # 1: locate the duplicated statements
            stmts0, stmts1 = block0.statements, block1.statements
            stmt_seqs = sub_lists(stmts0)
            matches = [(stmt_seq, list(pattern_in_seq(stmt_seq, stmts1))) for stmt_seq in stmt_seqs]
            match_seq, match_pos_in_1 = max(matches, key=lambda m: len(m[0]) if len(m[1]) > 0 else -1)

            if not match_pos_in_1:
                raise Exception("Matching blocks somehow have no matching statements!")

            if len(match_pos_in_1) != 1:
                raise Exception("There are too many matching statements in this block")

            # split the blocks statements based on the matching position
            match_pos_in_1 = match_pos_in_1[0]
            match_pos_in_0 = list(pattern_in_seq(match_seq, stmts0))[0]
            match_len = len(match_seq)
            merge_targets: Dict[int, MergeTarget] = {
                blk.addr: MergeTarget(blk, idx, match_len, self.copy_graph)
                for blk, idx in ((block0, match_pos_in_0), (block1, match_pos_in_1))
            }
            merge_block = merge_targets[block0.addr].merge_block

            # 2: destroy the old blocks that will be merged
            self.out_graph.remove_nodes_from((block0, block1))
            self.out_graph.add_node(merge_block)

            # 3: replace the edges of the pre blocks
            merge_trgt_preds = list()
            for _, trgt in merge_targets.items():
                merge_trgt_preds += trgt.predecessors

            for pred in set(merge_trgt_preds):
                if not isinstance(pred.statements[-1], ConditionalJump):
                    continue

                if_stmt: ConditionalJump = pred.statements[-1]
                for suc in self.copy_graph.successors(pred):
                    if suc.addr not in merge_targets:
                        continue

                    merge_target = merge_targets[suc.addr]
                    new_block = merge_target.pre_block if merge_target.pre_block else merge_block
                    self.out_graph.add_edge(pred, new_block)

                    new_target = if_stmt.true_target if if_stmt.true_target.value == suc.addr else if_stmt.false_target
                    new_target.value = new_block.addr


            # 4: make the pre blocks point to the merge block
            for _, trgt in merge_targets.items():
                if trgt.pre_block:
                    self.out_graph.add_edge(trgt.pre_block, merge_block)

            # 5: make the merge block point to the conditional clones
            # copy conditionals
            conditionals = list(self.copy_graph.predecessors(block0)) \
                if self.copy_graph.in_degree(block0) > self.copy_graph.in_degree(block1) \
                else list(self.copy_graph.predecessors(block1))

            # place conditionals in the output
            added_nodes = list()
            cond_graph: nx.DiGraph = self.copy_graph.subgraph(conditionals)
            for u, v in cond_graph.edges():
                new_u = ail_block_from_stmts([u.statements[-1]])
                new_u.addr += 1
                new_v = ail_block_from_stmts(v.statements)
                new_v.addr += 1
                self.out_graph.add_edge(new_u, new_v)
                added_nodes += [new_u, new_v]

            for node in added_nodes:
                if self.out_graph.in_degree(node) == 0:
                    break
            else:
                raise Exception("No ancestor node")

            self.out_graph.add_edge(merge_block, node)

            # 6: make the conditions go to the correct post blocks
            for node in added_nodes:
                if_stmt: ConditionalJump = node.statements[-1]
                for attr in ['false_target', 'true_target']:
                    target = getattr(if_stmt, attr)



                    if target.value == block0.addr:
                        if not post_block0:
                            new_target = post_block_suc0.addr
                            self.out_graph.add_edge(node, post_block_suc0)
                        else:
                            new_target = post_block0.addr
                            self.out_graph.add_edge(node, post_block0)
                        target.value = new_target

                    if target.value == block1.addr:
                        if not post_block1:
                            new_target = post_block_suc1.addr
                            self.out_graph.add_edge(node, post_block_suc1)
                        else:
                            new_target = post_block1.addr
                            self.out_graph.add_edge(node, post_block1)
                        target.value = new_target

            # 7: make the post blocks continue to the next successors
            for _, trgt in merge_targets.items():
                if trgt.post_block:
                    self.out_graph.add_edge(trgt.post_block, trgt.successors[0])

            return


AnalysesHub.register_default("BlockMerger", BlockMerger)
