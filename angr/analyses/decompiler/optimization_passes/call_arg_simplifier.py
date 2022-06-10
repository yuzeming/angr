from itertools import combinations
from typing import List

from ailment import Block, Const
from ailment.expression import Convert, Load

from ailment.statement import Statement, ConditionalJump, Jump, Assignment, Call, Store
import claripy

from angr.knowledge_plugins.key_definitions.constants import OP_AFTER
from .optimization_pass import OptimizationPass, OptimizationPassStage
from ....knowledge_plugins.key_definitions.atoms import MemoryLocation
from ..graph_region import GraphRegion
from ..region_identifier import RegionIdentifier, MultiNode
from ..utils import to_ail_supergraph

from ... import AnalysesHub

class CallArgSimplifier(OptimizationPass):
    """
    Simplifiy Args
    """
    ARCHES = ["X86", "AMD64", "ARMCortexM", "ARMHF", "ARMEL", ]
    PLATFORMS = ["cgc", "linux"]
    STAGE = OptimizationPassStage.DURING_REGION_IDENTIFICATION
    NAME = "Simplify Constat Prop Call Args"
    DESCRIPTION = __doc__.strip()

    def __init__(self, func, region_identifier=None, reaching_definitions=None, **kwargs):
        self.region_identifier = region_identifier
        self.rd = reaching_definitions
        super().__init__(func, **kwargs)

        self.analyze()

    def _check(self):
        return True, {}

    def _analyze(self, cache=None):
        """
        Entry analysis routine that will trigger the other analysis stages
        """
        self.out_graph = to_ail_supergraph(self._graph)
        try:
            for b0, b1 in combinations(self.out_graph.nodes, 2):
                call_info: List[Call] = self._contains_call((b0, b1))
                if not call_info:
                    continue

                # blocks must share a region
                if not self._share_subregion([b0, b1]):
                    continue

                c1, c2 = call_info[:]
                closeness = self._calls_close(c1, c2)
                if not closeness:
                    continue

                c1, c2, diff_dict = closeness
                for i, args in diff_dict.items():
                    a0, a1 = args[:]
                    const_call = c1 if isinstance(a0, Const) else c2
                    symb_call = c2 if const_call is c1 else c1
                    const_arg = a0 if isinstance(a0, Const) else a1
                    symb_arg = a1 if a0 is const_arg else a0
                    break

                const_blk = b0 if self.in_stmts(const_call, b0) else b1
                symb_blk = b1 if const_blk is b0 else b0

                symb_arg = symb_arg.operands[0] if isinstance(symb_arg, Convert) else symb_arg
                if not isinstance(symb_arg, Load):
                    continue

                sym_addr = symb_arg.addr.value

                target_atom = MemoryLocation(sym_addr, 4, 'Iend_LE')
                const_state = self.rd.get_reaching_definitions_by_node(const_blk.addr, OP_AFTER)
                state_load_vals = const_state.get_value_from_atom(target_atom)

                if not state_load_vals:
                    continue

                state_vals = state_load_vals.values
                if len(state_vals) > 1:
                    continue

                state_val = list(state_vals[0])[0]
                if hasattr(state_val, "concrete") and state_val.concrete:
                    const_value = claripy.Solver().eval(state_val, 1)[0]
                else:
                    continue

                if not const_value == const_arg.value:
                    continue

                const_call.args[i] = symb_call.args[i]
        except Exception:
            return self.out_graph


    def _calls_close(self, call1: Call, call2: Call, diff_max=1):
        if call1.likes(call2):
            return False
                
        c1 = call1 if len(call1.args) <= len(call2.args) else call2
        c2 = call2 if c1 is call1 else call1
        arg_len_diff = len(c2.args) - len(c1.args)
        diff_dict = {}
        for i, arg in enumerate(c1.args):
            if not arg.likes(c2.args[i]):
                diff_dict[i] = (arg, c2.args[i])

            if len(diff_dict) + arg_len_diff > diff_max:
                return False

        print("WON THE CALL!")
        print(f"{call1} ;;;;; {call2}")

        for _, args in diff_dict.items():
            if not any(isinstance(a, Const) for a in args):
                return False

        return c1, c2, diff_dict

    def _contains_call(self, blk):
        _b0, _b1 = blk[:]
        b0 = _b0 if len(_b0.statements) <= len(_b1.statements) else _b1
        b1 = _b1 if b0 is _b0 else _b0

        for i, stmt0 in enumerate(b0.statements):
            stmt1 = b1.statements[i]
            pair = stmt0, stmt1

            # two calls
            if all(isinstance(b, Call) for b in pair) and stmt0.target.likes(stmt1.target):
                return pair

            # two assignments of calls
            if all(isinstance(b, Assignment) for b in pair) and \
                    all(isinstance(b.src, Call) for b in pair) and \
                    stmt0.src.target.likes(stmt1.src.target):
                return [b.data for b in pair]

            # two stores of calls
            if all(isinstance(b, Store) for b in pair) and \
                    all(isinstance(b.data, Call) for b in pair) and \
                    stmt0.data.target.likes(stmt1.data.target):
                return [b.data for b in pair]

        return None

    def in_stmts(self, call, blk):
        for stmt in blk.statements:
            if call == stmt:
                return True

            if isinstance(stmt, Store) and stmt.data == call:
                return True

        return False


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

AnalysesHub.register_default("CallArgSimplifier", CallArgSimplifier)
