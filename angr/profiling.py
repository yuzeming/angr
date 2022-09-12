from asyncio.log import logger
import time
import pickle
from dataclasses import dataclass, field
from typing import Dict, Any, Optional
import logging

@dataclass
class ProfilingEventBase:
    timestamp: int = field(default_factory=time.time_ns)


@dataclass
class ProjectCreatedEvent(ProfilingEventBase):
    binary: str = ""
    options: Dict[str,Any] = field(default_factory=dict)


@dataclass
class StateCreatedEvent(ProfilingEventBase):
    state_id: str = ""
    addr: Optional[int] = -1
    parent_state_id: Optional[str] = None


@dataclass
class StateStashedEvent(ProfilingEventBase):
    state_id: str = ""
    stash_name: str = None


@dataclass
class StateErroredEvent(ProfilingEventBase):
    state_id: str = ""
    addr: Optional[int] = None


class Profiling:
    """
    This class saves limited profiling information about several angr events, including:

    - project creation
    - state creation
    - state termination
    """

    def __init__(self, log_path):
        self.log_path = log_path
        self.logger = logging.getLogger("ANGR_PRPFILING")
        self.logger.setLevel(logging.INFO)
        self.logger.addHandler(logging.FileHandler(log_path,mode="a",encoding="utf-8",delay=False))

    def project_created(self, binary: str, options: Dict[str,Any]) -> None:
        self.logger.info(
            ProjectCreatedEvent(binary=binary, options=options)
        )

    def state_created(self, state_id: str, addr: Optional[int], parent_state_id: Optional[str]) -> None:
        self.logger.info(
            StateCreatedEvent(state_id=state_id, addr=addr, parent_state_id=parent_state_id)
        )

    def state_stashed(self, state_id: str, stash_name: str) -> None:
        self.logger.info(
            StateStashedEvent(state_id=state_id, stash_name=stash_name)
        )

    def state_errored(self, state_id: str, addr: Optional[int]) -> None:
        self.logger.info(
            StateErroredEvent(state_id=state_id, addr=addr)
        )

