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
        test_gen_command: Command used to generate the test file.
        kill_check_command: Command used to check if mutant was killed.
    """

    mutant_name: str
    original_name: str
    status: MutantStatus
    execution_time: float  # seconds (kill check)
    test_gen_command: str = ""
    test_gen_time: float = 0.0  # seconds
    safety_check_time: float = 0.0  # seconds
    kill_check_command: str = ""
    stdout: str = ""
    stderr: str = ""

    def to_dict(self) -> dict[str, Any]:
        """Serialize to a JSON-compatible dict."""
        d = {
            "mutant_name": self.mutant_name,
            "original_name": self.original_name,
            "status": self.status.value,
            "execution_time": self.execution_time,
            "test_gen_command": self.test_gen_command,
            "test_gen_time": self.test_gen_time,
            "safety_check_time": self.safety_check_time,
            "kill_check_command": self.kill_check_command,
        }
        if self.stdout:
            d["stdout"] = self.stdout
        if self.stderr:
            d["stderr"] = self.stderr
        return d

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "MutantResult":
        """Deserialize from a JSON-compatible dict."""
        return cls(
            mutant_name=data["mutant_name"],
            original_name=data["original_name"],
            status=MutantStatus(data["status"]),
            execution_time=float(data["execution_time"]),
            test_gen_command=data.get("test_gen_command", ""),
            kill_check_command=data.get("kill_check_command", ""),
        )
