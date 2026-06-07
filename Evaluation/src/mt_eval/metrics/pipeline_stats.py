"""PipelineStats dataclass for mutation testing pipeline statistics."""

from dataclasses import dataclass
from typing import Any


@dataclass
class PipelineStats:
    """Aggregated pipeline statistics including not-supported tracking.

    Attributes:
        total_programs: Total number of programs in the evaluation.
        not_supported_programs: Programs that failed safety check.
        total_mutants: Total mutants across all programs.
        not_supported_mutants: Mutants skipped due to safety check failure.
        killed: Mutants classified as killed.
        survived: Mutants classified as survived.
        timeout: Mutants that timed out during kill check.
        error: Mutants that errored during kill check.
        total_num_tests: Total number of generated test methods.
        avg_num_tests: Average number of tests per program.
        median_num_tests: Median number of tests per program.
    """

    total_programs: int
    not_supported_programs: int
    total_mutants: int
    not_supported_mutants: int
    killed: int
    survived: int
    timeout: int
    error: int
    total_num_tests: int = 0
    avg_num_tests: float = 0.0
    median_num_tests: float = 0.0

    @property
    def supported_mutants(self) -> int:
        return self.total_mutants - self.not_supported_mutants

    @property
    def kill_rate(self) -> float:
        """Killed / supported_mutants. 0.0 if no supported mutants."""
        return self.killed / self.supported_mutants if self.supported_mutants > 0 else 0.0

    @property
    def not_survived_rate(self) -> float:
        """(Killed + timeout) / supported_mutants. 0.0 if no supported mutants."""
        return (self.killed + self.timeout) / self.supported_mutants if self.supported_mutants > 0 else 0.0

    @property
    def not_supported_program_rate(self) -> float:
        return self.not_supported_programs / self.total_programs if self.total_programs > 0 else 0.0

    @property
    def not_supported_mutant_rate(self) -> float:
        return self.not_supported_mutants / self.total_mutants if self.total_mutants > 0 else 0.0

    def to_dict(self) -> dict[str, Any]:
        """Serialize to JSON-compatible dict including computed properties."""
        return {
            "total_programs": self.total_programs,
            "not_supported_programs": self.not_supported_programs,
            "not_supported_program_rate": round(self.not_supported_program_rate, 4),
            "total_mutants": self.total_mutants,
            "not_supported_mutants": self.not_supported_mutants,
            "not_supported_mutant_rate": round(self.not_supported_mutant_rate, 4),
            "supported_mutants": self.supported_mutants,
            "killed": self.killed,
            "survived": self.survived,
            "timeout": self.timeout,
            "error": self.error,
            "kill_rate": round(self.kill_rate, 4),
            "not_survived_rate": round(self.not_survived_rate, 4),
            "total_num_tests": self.total_num_tests,
            "avg_num_tests": round(self.avg_num_tests, 2),
            "median_num_tests": self.median_num_tests,
        }
