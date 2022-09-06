# pylint:disable=multiple-statements,line-too-long,consider-using-enumerate
from typing import Dict, Set, Optional, Any, List, Union, Tuple, TYPE_CHECKING
import logging
import itertools
from collections import defaultdict

import networkx

import claripy
import ailment

from ...knowledge_plugins.cfg import IndirectJump, IndirectJumpType
from .. import Analysis, register_analysis
from ..cfg.cfg_utils import CFGUtils
from .region_identifier import GraphRegion
from .structurer_nodes import BaseNode, SequenceNode, CodeNode, ConditionNode, ConditionalBreakNode, LoopNode, \
    SwitchCaseNode, BreakNode, ContinueNode, EmptyBlockNotice, MultiNode, CascadingConditionNode
from .empty_node_remover import EmptyNodeRemover
from .jumptable_entry_condition_rewriter import JumpTableEntryConditionRewriter
from .condition_processor import ConditionProcessor
from .utils import remove_last_statement, extract_jump_targets, get_ast_subexprs, switch_extract_cmp_bounds, \
    insert_node
from .region_simplifiers.cascading_cond_transformer import CascadingConditionTransformer

if TYPE_CHECKING:
    from ...knowledge_plugins.functions import Function

l = logging.getLogger(name=__name__)


#
# The main analysis
#


class RecursiveStructurer(Analysis):
    """
    Recursively structure a region and all of its subregions.
    """
    def __init__(self, region, cond_proc=None, func: Optional['Function']=None):
        self._region = region
        self.cond_proc = cond_proc if cond_proc is not None else ConditionProcessor(self.project.arch)
        self.function = func

        self.result = None

        self._analyze()

    def _analyze(self):

        region = self._region.recursive_copy()
        self._case_entry_to_switch_head: Dict[int,int] = self._get_switch_case_entries()

        # visit the region in post-order DFS
        parent_map = { }
        stack = [ region ]

        while stack:
            current_region = stack[-1]

            has_region = False
            for node in networkx.dfs_postorder_nodes(current_region.graph, current_region.head):
                subnodes = [ ]
                if type(node) is GraphRegion:
                    if node.cyclic:
                        subnodes.append(node)
                    else:
                        subnodes.insert(0, node)
                    parent_map[node] = current_region
                    has_region = True
                stack.extend(subnodes)

            if not has_region:
                # pop this region from the stack
                stack.pop()

                # Get the parent region
                parent_region = parent_map.get(current_region, None)
                # structure this region
                st = self.project.analyses.Structurer(current_region, parent_map=parent_map,
                                                      condition_processor=self.cond_proc,
                                                      case_entry_to_switch_head=self._case_entry_to_switch_head,
                                                      func=self.function)
                # replace this region with the resulting node in its parent region... if it's not an orphan
                if not parent_region:
                    # this is the top-level region. we are done!
                    self.result = st.result
                    break

                self._replace_region(parent_region, current_region, st.result)

        # rewrite conditions in the result to remove all jump table entry conditions
        rewriter = JumpTableEntryConditionRewriter(set(itertools.chain(*self.cond_proc.jump_table_conds.values())))
        rewriter.walk(self.result)  # update SequenceNodes in-place

        # remove empty nodes (if any)
        self.result = EmptyNodeRemover(self.result).result

        # remove conditional jumps
        #Structurer._remove_conditional_jumps(self.result)

        self.result = self.cond_proc.remove_claripy_bool_asts(self.result)

    @staticmethod
    def _replace_region(parent_region, sub_region, node):

        parent_region.replace_region(sub_region, node)

    def _get_switch_case_entries(self) -> Dict[int,int]:

        if self.function is None:
            return {}

        entries = {}
        func_block_addrs = self.function.block_addrs_set

        jump_tables = self.kb.cfgs['CFGFast'].jump_tables
        for jump_table_head_addr, jumptable in jump_tables.items():
            if jump_table_head_addr not in func_block_addrs:
                continue
            for entry_addr in jumptable.jumptable_entries:
                entries[entry_addr] = jump_table_head_addr

        return entries


class Structurer(Analysis):
    """
    Structure a region.

    The current function graph is provided so that we can detect certain edge cases, for example, jump table entries no
    longer exist due to empty node removal during structuring or prior steps.
    """
    def __init__(self, region, parent_map=None, condition_processor=None, func: Optional['Function']=None,
                 case_entry_to_switch_head: Optional[Dict[int,int]]=None):

        self._region: GraphRegion = region
        self._parent_map = parent_map
        self.function = func
        self._case_entry_to_switch_head = case_entry_to_switch_head

        self.cond_proc = condition_processor if condition_processor is not None \
            else ConditionProcessor(self.project.arch)

        # intermediate states
        self._new_sequences = [ ]

        self.result = None

        self._analyze()

    def _analyze(self):

        has_cycle = self._has_cycle()
        # sanity checks
        if self._region.cyclic:
            if not has_cycle:
                l.critical("Region %r is supposed to be a cyclic region but there is no cycle inside. This is usually "
                           "due to the existence of loop headers with more than one in-edges, which angr decompiler "
                           "does not support yet. The decompilation result will be wrong.", self._region)
            self._analyze_cyclic()
        else:
            if has_cycle:
                l.critical("Region %r is supposed to be an acyclic region but there are cycles inside. This is usually "
                           "due to the existence of loop headers with more than one in-edges, which angr decompiler "
                           "does not support yet. The decompilation result will be wrong.", self._region)
            self._analyze_acyclic()

    def _analyze_cyclic(self):
        pass

    def _analyze_acyclic(self):
        # let's generate conditions first
        self.cond_proc.recover_reaching_conditions(self._region, with_successors=True,
                                                   case_entry_to_switch_head=self._case_entry_to_switch_head)

        # make the sequence node and pack reaching conditions into CodeNode instances
        seq = self._make_sequence()

        self._new_sequences.append(seq)

        while self._new_sequences:
            seq_ = self._new_sequences.pop(0)
            if len(seq_.nodes) <= 1:
                continue
            self._structure_sequence(seq_)

        seq = EmptyNodeRemover(seq).result

        # unpack nodes and remove CodeNode wrappers
        seq = self._unpack_sequence(seq)

        self.result = seq

    def _has_cycle(self):
        """
        Test if the region contains a cycle.

        :return: True if the region contains a cycle, False otherwise.
        :rtype: bool
        """

        return not networkx.is_directed_acyclic_graph(self._region.graph)

    def _structure_sequence(self, seq):

        self._make_ites(seq)
        empty_node_remover = EmptyNodeRemover(seq)
        new_seq = empty_node_remover.result
        # update self._new_sequences
        self._update_new_sequences(set(empty_node_remover.removed_sequences), empty_node_remover.replaced_sequences)

        # we need to do it in-place
        seq.nodes = new_seq.nodes

        while True:
            r, seq = self._merge_nesting_conditionals(seq)
            if r: continue
            break

    def _make_sequence(self):

        seq = SequenceNode(None)

        for node in CFGUtils.quasi_topological_sort_nodes(self._region.graph):
            seq.add_node(CodeNode(node, self.cond_proc.reaching_conditions.get(node, None)))

        if seq.nodes:
            seq.addr = seq.nodes[0].addr

        return seq

    @staticmethod
    def _unpack_sequence(seq):

        def _handle_Code(node, **kwargs):  # pylint:disable=unused-argument
            node = node.node
            return walker._handle(node)

        def _handle_Sequence(node, **kwargs):  # pylint:disable=unused-argument
            for i in range(len(node.nodes)):  # pylint:disable=consider-using-enumerate
                node.nodes[i] = walker._handle(node.nodes[i])
            return node

        def _handle_ConditionNode(node, **kwargs):  # pylint:disable=unused-argument
            if node.true_node is not None:
                node.true_node = walker._handle(node.true_node)
            if node.false_node is not None:
                node.false_node = walker._handle(node.false_node)
            return node

        def _handle_CascadingConditionNode(node: CascadingConditionNode, **kwargs):  # pylint:disable=unused-argument
            new_cond_and_nodes = [ ]
            for cond, child_node in node.condition_and_nodes:
                new_cond_and_nodes.append((cond, walker._handle(child_node)))
            node.condition_and_nodes = new_cond_and_nodes

            if node.else_node is not None:
                node.else_node = walker._handle(node.else_node)
            return node

        def _handle_SwitchCaseNode(node, **kwargs):  # pylint:disable=unused-argument
            for i in list(node.cases.keys()):
                node.cases[i] = walker._handle(node.cases[i])
            if node.default_node is not None:
                node.default_node = walker._handle(node.default_node)
            return node

        def _handle_Default(node, **kwargs):  # pylint:disable=unused-argument
            return node

        handlers = {
            CodeNode: _handle_Code,
            SequenceNode: _handle_Sequence,
            ConditionNode: _handle_ConditionNode,
            CascadingConditionNode: _handle_CascadingConditionNode,
            SwitchCaseNode: _handle_SwitchCaseNode,
            # don't do anything
            LoopNode: _handle_Default,
            ContinueNode: _handle_Default,
            ConditionalBreakNode: _handle_Default,
            BreakNode: _handle_Default,
            MultiNode: _handle_Default,
            ailment.Block: _handle_Default,
        }

        walker = SequenceWalker(handlers=handlers)
        walker.walk(seq)

        return seq

    def _update_new_sequences(self, removed_sequences: Set[SequenceNode], replaced_sequences: Dict[SequenceNode,Any]):
        new_sequences = [ ]
        for new_seq_ in self._new_sequences:
            if new_seq_ not in removed_sequences:
                if new_seq_ in replaced_sequences:
                    replaced = replaced_sequences[new_seq_]
                    if isinstance(replaced, SequenceNode):
                        new_sequences.append(replaced)
                else:
                    new_sequences.append(new_seq_)
        self._new_sequences = new_sequences

    #
    # If-statements
    #

    def _make_ite(self, seq):
        pass

    def _make_ites(self, seq):
        pass

    def _merge_nesting_conditionals(self, seq):

        # find if(A) { if(B) { ... ] } and simplify them to if( A && B ) { ... }

        def _condnode_truenode_only(node):
            if type(node) is CodeNode:
                # unpack
                node = node.node
            if isinstance(node, ConditionNode) and \
                    node.true_node is not None and \
                    node.false_node is None:
                return True, node
            return False, None

        def _condbreaknode(node):
            if type(node) is CodeNode:
                # unpack
                node = node.node
            if isinstance(node, SequenceNode):
                if len(node.nodes) != 1:
                    return False, None
                node = node.nodes[0]
                return _condbreaknode(node)
            if isinstance(node, ConditionalBreakNode):
                return True, node
            return False, None

        def _handle_SequenceNode(seq_node, parent=None, index=0, label=None):  # pylint:disable=unused-argument
            i = 0
            while i < len(seq_node.nodes):
                node = seq_node.nodes[i]
                r, cond_node = _condnode_truenode_only(node)
                if r:
                    r, cond_node_inner = _condnode_truenode_only(cond_node.true_node)
                    if r:
                        # amazing!
                        merged_cond = ConditionProcessor.simplify_condition(
                            claripy.And(self.cond_proc.claripy_ast_from_ail_condition(cond_node.condition),
                                        cond_node_inner.condition))
                        new_node = ConditionNode(cond_node.addr,
                                                 None,
                                                 merged_cond,
                                                 cond_node_inner.true_node,
                                                 None
                                                 )
                        seq_node.nodes[i] = new_node
                        walker.merged = True
                        i += 1
                        continue
                    # else:
                    r, condbreak_node = _condbreaknode(cond_node.true_node)
                    if r:
                        # amazing!
                        merged_cond = ConditionProcessor.simplify_condition(
                            claripy.And(self.cond_proc.claripy_ast_from_ail_condition(cond_node.condition),
                                        condbreak_node.condition))
                        new_node = ConditionalBreakNode(condbreak_node.addr, merged_cond, condbreak_node.target)
                        seq_node.nodes[i] = new_node
                        walker.merged = True
                        i += 1
                        continue

                walker._handle(node, parent=seq_node, index=i)

                i += 1

        handlers = {
            SequenceNode: _handle_SequenceNode,
        }

        walker = SequenceWalker(handlers=handlers)
        walker.merged = False  # this is just a hack
        walker.walk(seq)

        return walker.merged, seq


register_analysis(RecursiveStructurer, 'RecursiveStructurer')
register_analysis(Structurer, 'Structurer')

# delayed import
from .sequence_walker import SequenceWalker  # pylint:disable=wrong-import-position
