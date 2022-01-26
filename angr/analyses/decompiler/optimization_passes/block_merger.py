from typing import List, Tuple, Optional, Dict
import logging
import copy

import networkx
import networkx as nx

from ailment.block import Block
from ailment.statement import Statement, ConditionalJump, Call, Jump
from ailment.expression import Const, BinaryOp

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
        while shift <= pos and pattern[pos] != pattern[pos - shift]:
            shift += shifts[pos - shift]
        shifts[pos + 1] = shift

    # do the actual search
    start_pos = 0
    match_len = 0
    for c in seq:
        while match_len == len(pattern) or match_len >= 0 and pattern[match_len] != c:
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

    def _shares_common_path(self, node1, node2):
        pre1 = list(self.copy_graph.predecessors(node1))
        pre2 = list(self.copy_graph.predecessors(node2))
        ans1 = list(nx.algorithms.ancestors(self.copy_graph, node1))
        ans2 = list(nx.algorithms.ancestors(self.copy_graph, node2))

        return all([p1 in ans2 for p1 in pre1]) and all([p2 in ans1 for p2 in pre2])

    #
    # Analysis stages
    #

    def _fast_find_initial_candidates(self) -> List[Tuple[Block, Block]]:
        init_candidates = []
        for block in self.copy_graph.nodes():
            if block.statements and isinstance(block.statements[-1], ConditionalJump):
                successors: List[Block] = list(self.copy_graph.successors(block))
                if len(successors) == 2:
                    succ1, succ2 = successors[:]
                    for stmt in succ1.statements:
                        if stmt in succ2.statements:
                            init_candidates.append((succ1, succ2))
                            break

        return init_candidates

    def _filter_candidates(self, candidates):
        """
        Preform a series of filters on the candidates to reduce the fast set to an assured set of
        the duplication case we are searching for.

        TODO: need a way to group candidates that are more than a single pair, see if-else example
        """
        filtered_candidates = []
        for block00, block01 in candidates:
            if not self._shares_common_path(block00, block01):
                continue

            filtered_candidates.append((block00, block01))

        return filtered_candidates

    def _analyze(self, cache=None):
        """
        Entry analysis routine that will trigger the other analysis stages
        """
        return
        # do all writes on out_graph and all reads on copy_graph
        self.out_graph = to_ail_supergraph(self._graph)
        self.copy_graph = self.out_graph.copy()

        candidates = self._fast_find_initial_candidates()
        if not candidates:
            print("There are no duplicate statements in this function")
            return

        #candidates = self._filter_candidates(candidates)
        if not candidates:
            print("There are no duplicate blocks in this function")
            return

        print(f"CANDIDATES FOUND: {candidates}")
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
                    print(f"not conditional {pred}")
                    continue

                import ipdb; ipdb.set_trace()
                if_stmt: ConditionalJump = pred.statements[-1]
                for suc in self.copy_graph.successors(pred):
                    if suc.addr not in merge_targets:
                        print(f"skipping, {hex(suc.addr)} | {suc}")
                        continue
                    print(f"working on {hex(suc.addr)} | {suc}")

                    merge_target = merge_targets[suc.addr]
                    new_block = merge_target.pre_block if merge_target.pre_block else merge_block
                    self.out_graph.add_edge(pred, new_block)

                    new_target = if_stmt.true_target if if_stmt.true_target.value == suc.addr else if_stmt.false_target
                    print(f"updating {new_target} OF {if_stmt} WITH {hex(new_target.value)}")
                    new_target.value = new_block.addr
                    print(f"now: {new_target}")


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
            return
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
