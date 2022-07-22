from .refactor_pass import RefactorPass
from ..structurer_nodes import ConditionNode


CascadingIfElseCase = -1


class ConditionNodeSwapScopes(RefactorPass):
    NAME = "Swap the two branches of a condition node"

    def __init__(self, node: ConditionNode):
        super().__init__()
        self._node = node

        if self._node.true_node is not None and self._node.false_node is not None:
            self._analyze()

    def _analyze(self):
        new_node = ConditionNode(
            self._node.addr,
            self._node.reaching_condition,
            self._node.condition,
            self._node.false_node,
            self._node.true_node,
        )
        self.out_node = new_node
