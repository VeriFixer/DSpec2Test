"""Abstract base class for test generators."""

from abc import ABC, abstractmethod
from dataclasses import dataclass
from pathlib import Path


@dataclass
class TestGenResult:
    """Result of a test generation attempt."""

    success: bool
    test_file: Path | None
    error_message: str = ""
    command: str = ""
    execution_time: float = 0.0  # seconds


class TestGenerator(ABC):
    """Abstract interface for test generators.

    Subclass and implement generate_tests to add new generators
    without modifying pipeline code.
    """

    def __init__(self, name: str, **kwargs) -> None:
        self.name = name

    @abstractmethod
    def generate_tests(self, dafny_file: Path, output_file: Path) -> TestGenResult:
        """Receive a Dafny file, produce a new Dafny file with tests appended."""
        ...
