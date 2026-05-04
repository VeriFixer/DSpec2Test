"""MutantResult model and MutantStatus enum for mutation testing evaluation."""

from dataclasses import dataclass
from enum import Enum
from typing import Any


class MutantStatus(Enum):
    """Status of a mutant after test execution."""

    KILLED = "killed"
    SURVIVED = "survived"
    TIMEOUT = "timeout"
    ERROR = "error"


@dataclass
class MutantResult:
    """Result of running a test suite against a single mutant.

    Attributes:
        mutant_name: Filename of the mutant .dfy file.
        original_name: Filename of the original .dfy file.
        status: Outcome of test execution.
        execution_time: Wall-clock seconds for test execution.
    """

    mutant_name: str
    original_name: str
    status: MutantStatus
    execution_time: float  # seconds

    def to_dict(self) -> dict[str, Any]:
        """Serialize to a JSON-compatible dict."""
        return {
            "mutant_name": self.mutant_name,
            "original_name": self.original_name,
            "status": self.status.value,
            "execution_time": self.execution_time,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "MutantResult":
        """Deserialize from a JSON-compatible dict."""
        return cls(
            mutant_name=data["mutant_name"],
            original_name=data["original_name"],
            status=MutantStatus(data["status"]),
            execution_time=float(data["execution_time"]),
        )
