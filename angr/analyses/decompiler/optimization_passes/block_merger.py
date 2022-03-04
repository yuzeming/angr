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


def ail_block_from_stmts(stmts, idx=None, block_addr=None) -> Optional[Block]:
    if not stmts:
        return None

    first_stmt = stmts[0]

    return Block(
        first_stmt.tags['ins_addr'] if not block_addr else block_addr,
        0,
        statements=stmts,
        idx=idx or 1,
    )


def split_ail_block(block, split_idx, split_len) -> Tuple[Optional[Block], Optional[Block], Optional[Block]]:
    if split_len == len(block.statements):
        return None, block, None

    pre_split = ail_block_from_stmts(block.statements[:split_idx])
    merge_split = ail_block_from_stmts(block.statements[split_idx:split_idx + split_len])
    post_split = ail_block_from_stmts(block.statements[split_idx + split_len:])

    return pre_split, merge_split, post_split


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


def copy_graph_and_nodes(graph: nx.DiGraph) -> nx.DiGraph:
    new_graph = networkx.DiGraph()
    for node in graph.nodes:
        #    graph.add_node(ail_block_from_stmts(node.statements, block_addr=node.addr))
        new_graph.add_node(node.copy())

    for edge in graph.edges:
        old_b0, old_b1 = edge
        b0, b1 = find_block_by_addr(new_graph, old_b0.addr), find_block_by_addr(new_graph, old_b1.addr)
        new_graph.add_edge(b0, b1)

    return new_graph



#
# Longest Common Substring Helpers
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


def correct_conditional_jump(cond_stmt_param: ConditionalJump, replacement_map: Dict[int, int], new_stmt=False):
    cond_stmt = deepcopy_ail_condjump(cond_stmt_param) if new_stmt else cond_stmt_param
    true_target, false_target = cond_stmt.true_target, cond_stmt.false_target

    if true_target.value in replacement_map:
        true_target.value = replacement_map[true_target.value]

    if false_target.value in replacement_map:
        false_target.value = replacement_map[false_target.value]

    return cond_stmt


def clone_graph_with_splits(graph_param: nx.DiGraph, split_map_param):
    split_map = {
        block.addr: new_node for block, new_node in split_map_param.items()
    }

    graph = copy_graph_and_nodes(graph_param)
    breakpoint()
    # this loop will continue to iterate until there are no more
    # nodes found in the split_map to change
    while True:
        for node in graph.nodes():
            # TODO: source of problems:
            # now we are moddifying a block directly which is causing later analysis to get corrupted
            # now happening because of the way we are grabbing statements
            try:
                new_node = split_map[node.addr]
            except KeyError:
                continue

            if new_node == node:
                continue

            break
        else:
            break


        graph.add_node(new_node)
        for pred in graph.predecessors(node):
            last_stmt = pred.statements[-1]
            if isinstance(last_stmt, ConditionalJump):
                pred.statements[-1] = correct_conditional_jump(last_stmt, {node.addr: new_node.addr}, new_stmt=True)

            graph.add_edge(pred, new_node)

        for succ in graph.successors(node):
            graph.add_edge(new_node, succ)

        graph.remove_node(node)
    breakpoint()
    for node in graph.nodes():
        last_stmt = node.statements[-1]
        if isinstance(last_stmt, ConditionalJump):
            node.statements[-1] = correct_conditional_jump(
                last_stmt, {orig_addr: new.addr for orig_addr, new in split_map.items()},
                new_stmt=True
            )

    return graph


#
# OLD SHIT
#

def sub_lists(seq):
    lists = [[]]
    for i in range(len(seq) + 1):
        for j in range(i):
            lists.append(seq[j: i])
    return lists


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




def lcs_ail_stmts(blocks, graph=None, partial=False):
    print(f"RUNNING LCS ON {blocks}")
    # generate the lcs for each pair
    lcs_list = list()
    for b0, b1 in combinations(blocks, 2):
        stmts0, stmts1 = b0.statements, b1.statements
        stmt_seqs = sub_lists(stmts0)
        matches = [(stmt_seq, list(_kmp_search_ail_obj(stmt_seq, stmts1, graph=graph, partial=partial))) for stmt_seq in stmt_seqs]
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
            if all(True if len(list(_kmp_search_ail_obj(lcs, other_lcs, graph=graph, partial=partial))) > 0 else False for other_lcs in lcs_list):
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
        block_idxs[block] = list(_kmp_search_ail_obj(lcs, block.statements, graph=graph, partial=partial))[0]

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


def ail_graph_similarity(block0: Block, block1: Block, graph: nx.DiGraph, only_blocks=False):
    all_blocks = []

    # traverse all the blocks in BFS with True targets being first in children
    for block in [block0, block1]:
        blocks = list()
        bfs = list(nx.bfs_successors(graph, block, depth_limit=10))

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

        blocks = [block] + blocks
        all_blocks.append(blocks)

    b0_blocks = all_blocks[0]
    b1_blocks = all_blocks[1]
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
    traversal_blocks = list()
    bfs = list(nx.bfs_successors(graph, orig_block, depth_limit=10))

    for blk_tree in bfs:
        source, children = blk_tree

        if len(children) == 1:
            traversal_blocks += children
        elif len(children) == 2:
            if_stmt: ConditionalJump = source.statements[-1]
            if children[0].addr == if_stmt.true_target.value:
                traversal_blocks += [children[0], children[1]]
            else:
                traversal_blocks += [children[1], children[0]]

    traversal_blocks = [orig_block] + traversal_blocks

    graph_sim = graph_similarity.copy()
    orig_blocks = list()
    split_blocks = {}  # [block] = (lcs, idx)
    for block in traversal_blocks:
        if not graph_sim:
            break

        lcs, lcs_idxs = longest_ail_subseq([block.statements, graph_sim[:len(block.statements)]], graph=graph)
        if not lcs:
            break

        orig_blocks.append(block)
        split_blocks[block] = (lcs, lcs_idxs[0])

        graph_sim = graph_sim[len(lcs):]

    return orig_blocks, split_blocks






    """ 
    orig_stmt_len = len(orig_block.statements)
    lcs, _ = longest_ail_subseq([orig_block.statements, graph_similarity[:orig_stmt_len]], graph=graph)
    if not lcs:
        return []

    graph_similarity = graph_similarity[len(lcs):]
    if len(graph_similarity) == 0:
        return [orig_block]

    successors = list(graph.successors(orig_block))
    if len(successors) == 1:
        return [orig_block] + ail_similarity_to_orig_blocks(successors[0], graph_similarity, graph)
    elif len(successors) == 2:
        if_stmt: ConditionalJump = orig_block.statements[-1]
        true_blk = successors[0] if successors[0].addr == if_stmt.true_target.value else successors[1]
        false_blk = successors[1] if true_blk == successors[0] else successors[0]

        orig_true_len = len(true_blk.statements)
        true_lcs, _ = longest_ail_subseq([true_blk.statements, graph_similarity[:orig_true_len]], graph=graph)
        true_lcs_len = len(true_lcs) if true_lcs else 0

        false_true_len = len(false_blk.statements)
        false_lcs, _ = longest_ail_subseq([false_blk.statements, graph_similarity[:orig_false_len]], graph=graph)
        false_lcs_len = len(false_lcs) if false_lcs else 0

        false_succ = list(graph.successors(false_blk))
        if true_blk in false_succ:
            false_graph_sim = graph_similarity[true_lcs_len:true_lcs_len + false_lcs_len] \
                + graph_similarity[true_lcs_len:]
        else:
            false_graph_sim = graph_similarity[true_lcs_len:]

        return [orig_block] + ail_similarity_to_orig_blocks(true_blk, graph_similarity, graph) + \
            ail_similarity_to_orig_blocks(false_blk, graph_similarity[true_lcs_len:], graph)

    return [orig_block]
    """


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
        block_diffs = ail_graph_similarity(blk0, blk1, graph)
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
            if graph_diff in common_graph_diffs:
                continue

            all_match = True
            for other_diff in similar_graph_diffs:
                # skip the same diff (not like similar)
                if graph_diff is other_diff:
                    continue

                if len(graph_diff) > len(other_diff):
                    all_match = False
                    break

                # iterate each block in each diff
                for i, block in enumerate(graph_diff):
                    # both the start and end can have a split
                    if i == 0 or i == len(graph_diff)-1:
                        if len(block.statements) > len(other_diff[i].statements):
                            all_match = False
                            break

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
            else:
                not_fixed = False

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
        return f"<MergeTarget: {{\npreds[{self.predecessor_map}],\npre_blocks[{self.pre_block_map}],\n"\
               f"post_blocks[{self.post_block_map}],\nsuccs[{self.successor_map}]\n}}"

    def __repr__(self):
        return str(self)


#
# Merger Optimization
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
                if isinstance(last_statement, ConditionalJump):
                    pred.statements[-1] = correct_conditional_jump(last_statement, {block.addr: succ.addr})
                elif isinstance(last_statement, Jump):
                    pred.statements[-1].target.value = succ.addr

                graph.add_edge(pred, succ)
            break

        if not remove_queue:
            break

        print(f"REMOVING IN SIMPLE_REDUNDANT_JUMP: {remove_queue}")
        graph.remove_nodes_from(remove_queue)
        change |= True

    return graph, change


def remove_simple_similar_blocks(graph: nx.DiGraph):
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
            b0_suc, b1_suc = set(graph.successors(b0)), set(graph.successors(b1))

            # blocks should have the same successors
            if b0_suc != b1_suc:
                continue

            if not b0.likes(b1):
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
                if isinstance(last_statement, ConditionalJump):
                    pred.statements[-1] = correct_conditional_jump(last_statement, {b1.addr: b0.addr})
                elif isinstance(last_statement, Jump):
                    pred.statements[-1].target.value = b0.addr

                graph.add_edge(pred, b0)

            graph.remove_node(b1)
            not_fixed = True
            change |= True

    return graph, change


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

    node = nodes[0]
    node_level = [node]
    seen_nodes = set()
    while node_level:
        # check if any of the nodes on the current level are dominaters to all nodes
        for cnode in node_level:
            if isinstance(cnode.statements[-1], ConditionalJump) \
                    and all(dominates(idoms, cnode, node) for node in nodes):
                return cnode

        # if no dominators found, move up a level
        seen_nodes.update(set(node_level))
        next_level = list(itertools.chain.from_iterable([list(graph.predecessors(cnode)) for cnode in node_level]))
        # only add nodes we have never seen
        node_level = set(next_level).difference(seen_nodes)

    else:
        return None

    """
    dominators = [idoms[node] for node in nodes]

    for dom in dominators:
        if isinstance(dom.statements[-1], ConditionalJump) and all(dominates(idoms, dom, node) for node in nodes):
            return dom

    return None
    """


def copy_cond_graph(merge_start_nodes, graph, idx=1):
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
    cond_graph: nx.DiGraph = nx.subgraph(graph, removed_node_map[merge_start_nodes[0]])

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
                curr_succ = find_block_by_addr(graph, target.value)
            except Exception as e:
                continue

            for new_target, pre_graph in pre_graphs_maps.items():
                if pre_graph.has_node(curr_succ):
                    target.value = new_target.addr
                    break

    return new_cond_graph, pre_graphs_maps


def generate_merge_targets(blocks, graph: nx.DiGraph) -> \
        Tuple[nx.DiGraph, Dict[int, MergeTarget]]:
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
            merge_ends = [node for node in merge_graph.nodes if merge_graph.out_degree(node) == 0]

            base_to_merge_end = {
                og: merge_end
                for og, merge_end in base_og_to_merge.items() if merge_end in merge_ends
            }

        if not og_to_split:
            merge_targets[block] = MergeTarget({}, {}, {}, {}, removable_graph)
            continue

        # create merge start association
        pred_map = {og_to_split[block][0]: list(graph.predecessors(block))}
        pre_block_map = {og_to_split[block][0]: block}

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

    ARCHES = ['AMD64', 'ARMEL', 'ARMHF', "ARMCortexM", ]
    PLATFORMS = ["cgc", "linux"]
    STAGE = OptimizationPassStage.AFTER_VARIABLE_RECOVERY

    def __init__(self, func, **kwargs):

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
        allowed_depth = 10
        curr_depth = 0

        self.exclusion_blocks = set()
        self.write_graph = self.simple_optimize_graph(self._graph)

        while True:
            if curr_depth >= allowed_depth:
                raise Exception("Exceeded max depth allowed for duplication fixing")

            curr_depth += 1

            # do all writes on write_graph and all reads on read_graph
            self.read_graph = self.write_graph.copy()

            #
            # 0: Find candidates with duplicated AIL statements
            #

            candidates = self._find_initial_candidates()
            if not candidates:
                print("There are no duplicate statements in this function")
                return

            candidates = self._filter_candidates(candidates)
            if not candidates:
                print("There are no duplicate blocks in this function")
                return

            # do longest candidates first
            candidates = sorted(candidates, key=lambda x: len(x))
            candidate = candidates.pop()
            print(f"CANDIDATE FOUND: {candidate}")

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

            # xxx: this can destroy things
            for node in merge_graph.nodes:
                last_stmt = node.statements[-1]
                all_succ = [suc.addr for suc in self.write_graph.successors(node)]
                if isinstance(last_stmt, ConditionalJump):
                    for attr in ["true_target", "false_target"]:
                        target = getattr(last_stmt, attr)
                        if target.value in all_succ:
                            continue

                        try:
                            new_succ = find_block_by_addr(self.write_graph, target.value)
                        except Exception:
                            continue

                        self.write_graph.add_edge(node, new_succ)
                elif isinstance(last_stmt, Jump):
                    try:
                        new_succ = find_block_by_addr(self.write_graph, target.value)
                    except Exception:
                        continue

                    self.write_graph.add_edge(node, new_succ)

            #
            # 3: clone the conditional graph
            #

            merge_end_to_cond_graph = {}
            # guarantees at least a single run
            for i, merge_end in enumerate(merge_ends):
                cond_graph, pre_graph_map = copy_cond_graph(candidate, self.read_graph, idx=i + 1)
                root_cond = [node for node in cond_graph.nodes if cond_graph.in_degree(node) == 0][0]
                merge_end_to_cond_graph[merge_end] = (root_cond, cond_graph)

            #
            # 4: replace the edges from the preds to the pre block
            #

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

                        self.write_graph.add_edge(pred, new_block)

                    if pre_blk:
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
                    post_blk = merge_target.post_block_map[merge_end]
                    new_block = post_blk if post_blk else merge_target.successor_map[merge_end][0]

                    for cond in cond_graph.nodes:
                        if_stmt: ConditionalJump = cond.statements[-1]
                        for attr in ["true_target", "false_target"]:
                            target = getattr(if_stmt, attr)
                            if target.value == block.addr:
                                target.value = new_block.addr
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
            # 8: fix the merge nodes
            #
            breakpoint()

            #breakpoint()
            #for node in merge_graph.nodes:
            #    last_statement = node.statements[-1]
            #    if isinstance(last_statement, ConditionalJump):
            #        if_stmt = node.statements[-1]
            #        for attr in ["true_target", "false_target"]:
            #            target = getattr(if_stmt, attr)
            #            all_succ = [suc.addr for suc in self.write_graph.successors(node)]

            #            if target.value in all_succ:
            #                continue

            #            try:
            #                new_succ = find_block_by_addr(self.write_graph, target.value)
            #            except Exception:
            #                continue

            #            self.write_graph.add_edge(node, new_succ)

            self.write_graph = self.simple_optimize_graph(self.write_graph)
            break

        self.out_graph = self.write_graph

    #
    # Search Stages
    #

    def _find_initial_candidates(self) -> List[Tuple[Block, Block]]:
        initial_candidates = list()
        for b0, b1 in combinations(self.read_graph.nodes, 2):
            if b0 in self.exclusion_blocks or b1 in self.exclusion_blocks:
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
                    if stmt0.likes(stmt1):
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

        """
        sim_list = {
            (b0, b1): ail_graph_similarity(b0, b1, self.read_graph, only_blocks=True) for b0, b1 in candidates
        }
        blks_in_sim = {
            (pair[0], pair[1]): set(itertools.chain.from_iterable([[sim[0], sim[1]] for sim in sims]))
            for pair, sims in sim_list.items()
        }
        """
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

                for pair, descendants in blk_descendants.items():
                    if pair == candidate:
                        continue

                    if all(c in descendants for c in candidate):
                        removal_queue.append(candidate)

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
        return candidates

    #
    # Simple Optimizations (for cleanup)
    #

    def simple_optimize_graph(self, graph):
        def _to_ail_supergraph(graph_):
            # make supergraph conversion always say no change
            return to_ail_supergraph(graph_), False

        new_graph = graph.copy()
        opts = [
            _to_ail_supergraph,
            remove_redundant_jumps,
            remove_simple_similar_blocks
        ]

        change = True
        while change:
            change = False
            for opt in opts:
                new_graph, has_changed = opt(new_graph)
                change |= has_changed

        return new_graph


AnalysesHub.register_default("BlockMerger", BlockMerger)