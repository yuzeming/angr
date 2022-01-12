from typing import List
import logging

from ailment.block import Block
from ailment.statement import Statement, ConditionalJump, Call, Jump
from ailment.expression import Const, BinaryOp

from ... import AnalysesHub
from .optimization_pass import OptimizationPass, OptimizationPassStage


_l = logging.getLogger(name=__name__)


def s2u(s, bits):
    if s > 0:
        return s
    return (1 << bits) + s


class BlockMerger(OptimizationPass):

    ARCHES = ['ARMEL', 'ARMHF', "ARMCortexM", ]
    PLATFORMS = ["cgc", "linux"]
    STAGE = OptimizationPassStage.AFTER_VARIABLE_RECOVERY

    def __init__(self, func, **kwargs):

        super().__init__(func, **kwargs)

        self.analyze()

    def _check(self):

        # TODO: More checks

        return True, { }

    def _analyze(self, cache=None):

        candidates = [ ]

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

        pairs = [ ]
        for block_00, block_01 in candidates:
            for block_10, block_11 in candidates:
                if len(block_00.statements) == 1 and len(block_10.statements) > 1 and str(block_00.statements[-1]) == str(block_10.statements[-1]):  # FIXME: don't use str()
                    # found it!
                    pairs.append((block_00, block_01, block_10, block_11))
                    break

        for block_00, block_01, block_10, block_11 in pairs:
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
