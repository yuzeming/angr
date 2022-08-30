
from ...code_location import CodeLocation
from typing import Tuple


class ExternalCodeLocation(CodeLocation):

    __slots__ = ("call_string", )

    def __init__(self, call_string: Tuple[int, ...]=None):
        super(ExternalCodeLocation, self).__init__(0, 0)
        self.call_string = call_string if call_string is not None else tuple()

    def __repr__(self):
        return f"[External {[hex(x) if isinstance(x, int) else x for x in self.call_string]}]"

    def __hash__(self):
        """
        returns the hash value of self.
        """
        if self._hash is None:
            self._hash = hash((self.block_addr, self.stmt_idx, self.sim_procedure, self.ins_addr, self.context, self.block_idx, self.call_string))
        return self._hash
