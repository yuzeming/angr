from typing import List, Tuple
import logging

import networkx as nx

from ailment.block import Block
from ailment.statement import Statement, ConditionalJump, Call, Jump
from ailment.expression import Const, BinaryOp

from ... import AnalysesHub
from .optimization_pass import OptimizationPass, OptimizationPassStage
from ..utils import to_ail_supergraph, SuperAILNode
from ....utils.graph import dominates


_l = logging.getLogger(name=__name__)


def s2u(s, bits):
    if s > 0:
        return s
    return (1 << bits) + s


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
        pre1 = list(self.super_graph.predecessors(node1))
        pre2 = list(self.super_graph.predecessors(node2))
        ans1 = list(nx.algorithms.ancestors(self.super_graph, node1))
        ans2 = list(nx.algorithms.ancestors(self.super_graph, node2))

        return all([p1 in ans2 for p1 in pre1]) and all([p2 in ans1 for p2 in pre2])

    #
    # Analysis stages
    #

    def _fast_find_initial_candidates(self) -> List[Tuple[SuperAILNode, SuperAILNode]]:
        init_candidates = []
        for block in self.super_graph.nodes():
            if block.statements and isinstance(block.statements[-1], ConditionalJump):
                successors: List[Block] = list(self.super_graph.successors(block))
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
        self.out_graph = self._graph.copy()
        self.super_graph = to_ail_supergraph(self._graph)

        candidates = self._fast_find_initial_candidates()
        if not candidates:
            raise Exception("There are no duplicate statements in this function")

        candidates = self._filter_candidates(candidates)
        if not candidates:
            raise Exception("There are no duplicate blocks in this function")

        return


        final_candidates = []
        for if_stmt, block_00, block_01 in candidates:
            removal_trgt = max((block_00, block_01), key=lambda b: len(list(super_graph.successors(b))))
            merge_trgt = block_00 if block_01 is removal_trgt else block_01

            # looking for a series of statements that starts in merge_trgt, and ends in removal_trgt
            for i, stmt in enumerate(merge_trgt.statements):
                if stmt != removal_trgt.statements[0]:
                    continue

                # sequence starts and ends the same
                common_sequence = merge_trgt.statements[i:]
                if common_sequence == removal_trgt.statements[:len(common_sequence)]:
                    final_candidates.append((if_stmt, merge_trgt, removal_trgt, i, len(common_sequence)))
                    print(f"FINAL CANDIDATES SELECTED\n{if_stmt}\n{merge_trgt}\n{removal_trgt}")

            else:
                continue

        for if_stmt, merge_trgt, removal_trgt, merge_split, common_len in final_candidates:
            #TODO: huge guess here, but every node only has one statement

            # split the super blocks back into nodes
            m1, m2 = merge_trgt.nodes[:merge_split], merge_trgt.nodes[merge_split:]
            r1, r2 = removal_trgt.nodes[:common_len], removal_trgt.nodes[common_len:]


            # destroy the old conditionals to r1 top
            r1_preds = list(self._graph.predecessors(r1[0]))
            r1_conds = []
            for pred in r1_preds:
                self.out_graph.remove_edge(pred, r1[0])

                # make them point to m2 now
                if isinstance(pred.statements[0], ConditionalJump):
                    # TODO: fixme
                    r1_conds.append(pred.statements[0].copy())
                    pred.statements[0].false_target = Const(None, None, m2.addr, self.project.arch.bits)

            # get rid of r1
            for node in r1:
                self.out_graph.remove_node(node)

            m2_succ = list(self._graph.successors(m2[-1]))
            assert len(m2_succ) == 1

            self.out_graph.remove_edge(m2[-1], m2_succ[0])

            for cond_node in r1_conds:
                pass





        candidates = []
        # find a block with a call and an immediate following branch
        for block_id, block in self.blocks_by_addr_and_idx.items():
            if block.statements and isinstance(block.statements[-1], Call):
                # check its successor
                successors: List[Block] = list(self._graph.successors(block))
                if len(successors) == 1:
                    succ = successors[0]
                    if succ.statements and isinstance(succ.statements[-1], ConditionalJump):
                        # found one
                        candidates.append((block, succ))

        final_candidates = [ ]
        for block_00, block_01 in candidates:
            for block_10, block_11 in candidates:
                if len(block_00.statements) == 1 and len(block_10.statements) > 1 and str(block_00.statements[-1]) == str(block_10.statements[-1]):  # FIXME: don't use str()
                    # found it!
                    final_candidates.append((block_00, block_01, block_10, block_11))
                    break

        for block_00, block_01, block_10, block_11 in final_candidates:
            # old blocks: block_10 + block_11
            # mirror block: block_00 + block_01

            # parse the condition at the end of block_01
            assert isinstance(block_01.statements[-1], ConditionalJump)
            assert isinstance(block_01.statements[-1].true_target, Const)
            assert isinstance(block_01.statements[-1].false_target, Const)
            block_01_cond = block_01.statements[-1].condition
            block_01_truetarget = block_01.statements[-1].true_target.value
            block_01_falsetarget = block_01.statements[-1].false_target.value

            mirror_block_successor = list(self._graph.successors(block_11))
            assert len(mirror_block_successor) == 2

            # TODO:

            new_block_10 = block_10.copy()
            new_block_10.statements = new_block_10.statements[:1]

            self._update_block(block_10, new_block_10)

            stmt: Statement = block_11.statements[-1]
            if isinstance(stmt, ConditionalJump):

                # TODO: do a proper condition matching instead of only testing the operator
                if stmt.condition.op == block_01_cond.op:
                    jump_to = block_01_truetarget
                elif stmt.condition.op == BinaryOp.COMPARISON_NEGATION[block_01_cond.op]:
                    jump_to = block_01_falsetarget
                else:
                    # we cannot handle it. give up
                    continue

                # block_11 ends with a conditional jump, too, where one target is the same as one of block_01's
                # branch targets, and the other is different
                # we just make block_11 jump to block_00
                block_11.statements[-1] = Jump(None, Const(None, None, block_00.addr, self.project.arch.bits),
                                               **stmt.tags)
            else:
                assert False

            for _, dst, data in list(self.out_graph.out_edges(block_11, data=True)):
                if dst.addr != jump_to:
                    # print(f"Adding a new edge {block_to_change}, {mirror_block}")
                    self.out_graph.add_edge(block_11, block_00, **data)
                    # print(f"Removing edge {block_to_change}, {dst}")
                    self.out_graph.remove_edge(block_11, dst)
                else:
                    self.out_graph.remove_edge(block_11, dst)



AnalysesHub.register_default("BlockMerger", BlockMerger)
