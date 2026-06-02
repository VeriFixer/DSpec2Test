"""DafnyTestGenerator — shared base class for Dafny generate-tests strategies."""

import subprocess
import time
from abc import abstractmethod
from pathlib import Path

from src.mt_eval.core.abstract import TestGenResult, TestGenerator
from src.mt_eval.execution.subprocess_utils import run_with_cleanup
from src import config


# Auto-registration registry populated by @register_strategy decorator
STRATEGY_REGISTRY: dict[str, type["DafnyTestGenerator"]] = {}


def register_strategy(name: str):
    """Class decorator that registers a DafnyTestGenerator subclass under *name*.

    Usage:
        @register_strategy("Spec")
        class SpecTestGenerator(DafnyTestGenerator): ...
    """
    def decorator(cls):
        cls.MODE = name
        STRATEGY_REGISTRY[name] = cls
        return cls
    return decorator


def _extract_test_methods(raw_output: str) -> str:
    """Extract test methods from dafny generate-tests output.

    Captures everything starting from the first comment line,
    discarding any include directives or warnings that precede it.
    """
    lines = raw_output.splitlines(keepends=True)
    for i, line in enumerate(lines):
        if "//" in line:
            return "".join(lines[i:]).strip()
    return ""


class DafnyTestGenerator(TestGenerator):
    """Base class for Dafny generate-tests strategies.

    Subclasses build the command via `_build_cmd()`.
    This class only executes it and processes the output.
    """

    def __init__(self, mode: str, **kwargs):
        super().__init__(name=f"DafnyTestGenerator_{mode}", **kwargs)
        self.mode = mode

    @abstractmethod
    def _build_cmd(self, dafny_file: Path) -> list[str]:
        """Build the dafny generate-tests command. Implemented by subclasses."""
        ...

    def generate_tests(self, dafny_file: Path, output_file: Path) -> TestGenResult:
        """Execute the command from _build_cmd() and return result.

        The output test file = original source + generated test methods at bottom.
        """
        cmd = self._build_cmd(dafny_file)
        cmd_str = " ".join(cmd)
        start = time.monotonic()
        try:
            result = run_with_cleanup(cmd, timeout=config.TESTGEN_TIMEOUT)
            elapsed = time.monotonic() - start
            if result.returncode == 0 and result.stdout.strip():
                test_methods = _extract_test_methods(result.stdout)
                if not test_methods:
                    return TestGenResult(
                        success=False,
                        test_file=None,
                        error_message="no test methods extracted from output",
                        command=cmd_str,
                        execution_time=elapsed,
                    )
                # Build test file: original content + test methods appended
                original_content = dafny_file.read_text()
                combined = original_content.rstrip() + "\n\n" + test_methods + "\n"

                output_file.parent.mkdir(parents=True, exist_ok=True)
                output_file.write_text(combined)
                return TestGenResult(success=True, test_file=output_file, command=cmd_str,
                                     execution_time=elapsed)

            # Build informative error message
            err_msg = ""
            if result.stderr and result.stderr.strip():
                err_lines = result.stderr.strip().splitlines()[:3]
                err_msg = "; ".join(err_lines)
            if not err_msg:
                err_msg = f"exit code {result.returncode}"
            elif result.returncode != 0:
                err_msg = f"exit code {result.returncode}: {err_msg}"

            return TestGenResult(
                success=False,
                test_file=None,
                error_message=err_msg,
                command=cmd_str,
                execution_time=elapsed,
            )
        except subprocess.TimeoutExpired:
            elapsed = time.monotonic() - start
            return TestGenResult(
                success=False, test_file=None, error_message="timeout", command=cmd_str,
                execution_time=elapsed,
            )
        except Exception as e:
            elapsed = time.monotonic() - start
            return TestGenResult(
                success=False, test_file=None, error_message=str(e), command=cmd_str,
                execution_time=elapsed,
            )
