from typing import Optional, Tuple, Any
from collections import defaultdict

import networkx

import networkx

import ailment

from .structurer_nodes import MultiNode, BaseNode, CodeNode, SequenceNode, ConditionNode, SwitchCaseNode, \
    CascadingConditionNode


def remove_last_statement(node):
    stmt = None

    if type(node) is CodeNode:
        stmt = remove_last_statement(node.node)
    elif type(node) is ailment.Block:
        stmt = node.statements[-1]
        node.statements = node.statements[:-1]
    elif type(node) is MultiNode:
        if node.nodes:
            stmt = remove_last_statement(node.nodes[-1])
            if BaseNode.test_empty_node(node.nodes[-1]):
                node.nodes = node.nodes[:-1]
    elif type(node) is SequenceNode:
        if node.nodes:
            stmt = remove_last_statement(node.nodes[-1])
            if BaseNode.test_empty_node(node.nodes[-1]):
                node.nodes = node.nodes[:-1]
    else:
        raise NotImplementedError()

    return stmt


def append_statement(node, stmt):

    if type(node) is CodeNode:
        append_statement(node.node, stmt)
        return
    if type(node) is ailment.Block:
        node.statements.append(stmt)
        return
    if type(node) is MultiNode:
        if node.nodes:
            append_statement(node.nodes[-1], stmt)
        else:
            raise NotImplementedError()
        return
    if type(node) is SequenceNode:
        if node.nodes:
            append_statement(node.nodes[-1], stmt)
        else:
            raise NotImplementedError()
        return

    raise NotImplementedError()


def replace_last_statement(node, old_stmt, new_stmt):

    if type(node) is CodeNode:
        replace_last_statement(node.node, old_stmt, new_stmt)
        return
    if type(node) is ailment.Block:
        if node.statements[-1] is old_stmt:
            node.statements[-1] = new_stmt
        return
    if type(node) is MultiNode:
        if node.nodes:
            replace_last_statement(node.nodes[-1], old_stmt, new_stmt)
        return
    if type(node) is SequenceNode:
        if node.nodes:
            replace_last_statement(node.nodes[-1], old_stmt, new_stmt)
        return
    if type(node) is ConditionNode:
        if node.true_node is not None:
            replace_last_statement(node.true_node, old_stmt, new_stmt)
        if node.false_node is not None:
            replace_last_statement(node.false_node, old_stmt, new_stmt)
        return

    raise NotImplementedError()


def extract_jump_targets(stmt):
    """
    Extract concrete goto targets from a Jump or a ConditionalJump statement.

    :param stmt:    The statement to analyze.
    :return:        A list of known concrete jump targets.
    :rtype:         list
    """

    targets = [ ]

    if isinstance(stmt, ailment.Stmt.Jump):
        if isinstance(stmt.target, ailment.Expr.Const):
            targets.append(stmt.target.value)
    elif isinstance(stmt, ailment.Stmt.ConditionalJump):
        if isinstance(stmt.true_target, ailment.Expr.Const):
            targets.append(stmt.true_target.value)
        if isinstance(stmt.false_target, ailment.Expr.Const):
            targets.append(stmt.false_target.value)

    return targets


def switch_extract_cmp_bounds(last_stmt: ailment.Stmt.ConditionalJump) -> Optional[Tuple[Any,int,int]]:
    """
    Check the last statement of the switch-case header node, and extract lower+upper bounds for the comparison.

    :param last_stmt:   The last statement of the switch-case header node.
    :return:            A tuple of (comparison expression, lower bound, upper bound), or None
    """

    if not isinstance(last_stmt, ailment.Stmt.ConditionalJump):
        return None

    # TODO: Add more operations
    if last_stmt.condition.op == 'CmpLE':
        if not isinstance(last_stmt.condition.operands[1], ailment.Expr.Const):
            return None
        cmp_ub = last_stmt.condition.operands[1].value
        cmp_lb = 0
        cmp = last_stmt.condition.operands[0]
        if isinstance(cmp, ailment.Expr.BinaryOp) and \
                cmp.op == 'Sub' and \
                isinstance(cmp.operands[1], ailment.Expr.Const):
            cmp_ub += cmp.operands[1].value
            cmp_lb += cmp.operands[1].value
            cmp = cmp.operands[0]
        return cmp, cmp_lb, cmp_ub

    return None


def get_ast_subexprs(claripy_ast):

    queue = [ claripy_ast ]
    while queue:
        ast = queue.pop(0)
        if ast.op == "And":
            queue += ast.args[1:]
            yield ast.args[0]
        else:
            yield ast


def insert_node(parent, insert_idx, node, node_idx, label=None, insert_location=None):

    if isinstance(parent, SequenceNode):
        parent.nodes.insert(insert_idx, node)
    elif isinstance(parent, CodeNode):
        # Make a new sequence node
        seq = SequenceNode(parent.addr, nodes=[parent.node, node])
        parent.node = seq
    elif isinstance(parent, MultiNode):
        parent.nodes.insert(insert_idx, node)
    elif isinstance(parent, ConditionNode):
        if node_idx == 0:
            # true node
            if not isinstance(parent.true_node, (SequenceNode, MultiNode)):
                parent.true_node = SequenceNode(parent.true_node.addr, nodes=[parent.true_node])
            insert_node(parent.true_node, insert_idx - node_idx, node, 0)
        else:
            # false node
            if not isinstance(parent.false_node, (SequenceNode, MultiNode)):
                parent.false_node = SequenceNode(parent.false_node.addr, nodes=[parent.false_node])
            insert_node(parent.false_node, insert_idx - node_idx, node, 0)
    elif isinstance(parent, CascadingConditionNode):
        cond, child_node = parent.condition_and_nodes[node_idx]
        if not isinstance(child_node, SequenceNode):
            child_node = SequenceNode(child_node.addr, nodes=[child_node])
            parent.condition_and_nodes[node_idx] = (cond, child_node)
        insert_node(child_node, insert_idx - node_idx, node, 0)
    elif isinstance(parent, SwitchCaseNode):
        # note that this case will be hit only when the parent node is not a container, such as SequenceNode or
        # MultiNode. we always need to create a new SequenceNode and replace the original node in place.
        if label == 'switch_expr':
            raise TypeError("You cannot insert a node after an expression.")
        if label == 'case':
            # node_idx is the case number
            if insert_location == 'after':
                new_nodes = [ parent.cases[node_idx], node ]
            elif insert_location == 'before':
                new_nodes = [ node, parent.cases[node_idx] ]
            else:
                raise TypeError("Unsupported 'insert_location' value %r." % insert_location)
            seq = SequenceNode(new_nodes[0].addr, nodes=new_nodes)
            parent.cases[node_idx] = seq
        elif label == 'default':
            if insert_location == 'after':
                new_nodes = [ parent.default_node, node ]
            elif insert_location == 'before':
                new_nodes = [ node, parent.default_node ]
            else:
                raise TypeError("Unsupported 'insert_location' value %r." % insert_location)
            seq = SequenceNode(new_nodes[0].addr, nodes=new_nodes)
            parent.default_node = seq
    else:
        raise NotImplementedError()


def _merge_ail_nodes(graph, node_a: ailment.Block, node_b: ailment.Block) -> ailment.Block:
    in_edges = list(graph.in_edges(node_a, data=True))
    out_edges = list(graph.out_edges(node_b, data=True))

    new_node = node_a.copy() if node_a.addr <= node_b.addr else node_b.copy()
    old_node = node_b if new_node == node_a else node_a
    new_node.statements += old_node.statements
    new_node.original_size += old_node.original_size

    graph.remove_node(node_a)
    graph.remove_node(node_b)

    if new_node is not None:
        graph.add_node(new_node)

        for src, _, data in in_edges:
            if src is node_b:
                src = new_node
            graph.add_edge(src, new_node, **data)

        for _, dst, data in out_edges:
            if dst is node_a:
                dst = new_node
            graph.add_edge(new_node, dst, **data)

    return new_node


def to_ail_supergraph(transition_graph: networkx.DiGraph) -> networkx.DiGraph:
    """
    Takes an AIL graph and converts it into a AIL graph that treats calls and redundant jumps
    as parts of a bigger block instead of transitions. Calls to returning functions do not terminate basic blocks.
    Based on region_identifier super_graph

    :return: A converted super transition graph
    """
    # make a copy of the graph
    transition_graph = networkx.DiGraph(transition_graph)

    # remove all edges that transitions to outside
    for src, dst, data in list(transition_graph.edges(data=True)):
        if data['type'] in ('transition', 'exception') and data.get('outside', False) is True:
            transition_graph.remove_edge(src, dst)
        # remove dead nodes
        if transition_graph.in_degree(dst) == 0:
            transition_graph.remove_node(dst)

    edges_to_shrink = set()

    # Find all edges to remove in the super graph
    for src in transition_graph.nodes():
        edges = transition_graph[src]

        # there are two types of edges we want to remove:
        # - call or fakerets, since we do not want blocks to break at calls
        # - boring jumps that directly transfer the control to the block immediately after the current block.

        if len(edges) == 1 and src.addr + src.original_size == next(iter(edges.keys())).addr:
            dst = next(iter(edges.keys()))
            dst_in_edges = transition_graph.in_edges(dst)
            if len(dst_in_edges) == 1:
                edges_to_shrink.add((src, dst))
                continue

        # skip anything that is not like a call
        if any(iter('type' in data and data['type'] not in ('fake_return', 'call') for data in edges.values())):
            continue

        for dst, data in edges.items():
            if 'type' in data and data['type'] == 'fake_return':
                if all(iter('type' in data and data['type'] in ('fake_return', 'return_from_call')
                            for _, _, data in transition_graph.in_edges(dst, data=True))):
                    edges_to_shrink.add((src, dst))
                break

    # Create the super graph
    super_graph = networkx.DiGraph()
    supernodes_map = {}

    for node in transition_graph.nodes():
        dests_and_data = transition_graph[node]

        # make a super node
        if node in supernodes_map:
            src_supernode = supernodes_map[node]
        else:
            src_supernode = SuperAILNode.from_ailnode(node)
            supernodes_map[node] = src_supernode
            # insert it into the graph
            super_graph.add_node(src_supernode)

        if not dests_and_data:
            # might be an isolated node
            continue

        # Take src_supernode off the graph since we might modify it
        if src_supernode in super_graph:
            existing_in_edges = list(super_graph.in_edges(src_supernode, data=True))
            existing_out_edges = list(super_graph.out_edges(src_supernode, data=True))
            super_graph.remove_node(src_supernode)
        else:
            existing_in_edges = [ ]
            existing_out_edges = [ ]

        for dst, data in dests_and_data.items():
            edge = (node, dst)

            if edge in edges_to_shrink:
                dst_supernode = supernodes_map.get(dst, None)
                src_supernode.insert_ailnode(dst)

                # update supernodes map
                supernodes_map[dst] = src_supernode

                break
        else:
            break

    return transition_graph
