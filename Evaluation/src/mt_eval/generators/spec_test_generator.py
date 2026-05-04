"""SpecTestGenerator — invokes `dafny generate-tests Spec` via subprocess."""

import subprocess
from pathlib import Path

from src.mt_eval.core.abstract import TestGenResult, TestGenerator
from src import config


class SpecTestGenerator(TestGenerator):
    """Concrete test generator using Dafny's generate-tests command (Spec mode).

    Uses the SpecTestGenerator fork binary which supports the 'Spec' mode.
    Output is captured from stdout and written to the output file.
    """

    def __init__(self, dafny_binary: Path | None = None, mode: str = "Spec",
                 test_count: int = 1, **kwargs):
        super().__init__(name="SpecTestGenerator", **kwargs)
        self.dafny_binary = dafny_binary or config.SPECTEST_DAFNY_BINARY
        self.mode = mode
        self.test_count = test_count

    def generate_tests(self, dafny_file: Path, output_file: Path) -> TestGenResult:
        """Run dafny generate-tests Spec and return result."""
        cmd = [
            str(self.dafny_binary),
            "generate-tests",
            self.mode,
            str(dafny_file.resolve()),
            "--test-count",
            str(self.test_count),
        ]
        try:
            result = subprocess.run(
                cmd,
                timeout=config.TESTGEN_TIMEOUT,
                capture_output=True,
                text=True,
            )
            if result.returncode == 0 and result.stdout.strip():
                output_file.parent.mkdir(parents=True, exist_ok=True)
                output_file.write_text(result.stdout)
                return TestGenResult(success=True, test_file=output_file)
            return TestGenResult(
                success=False,
                test_file=None,
                error_message=result.stderr or f"exit code {result.returncode}",
            )
        except subprocess.TimeoutExpired:
            return TestGenResult(
                success=False, test_file=None, error_message="timeout"
            )
        except Exception as e:
            return TestGenResult(
                success=False, test_file=None, error_message=str(e)
            )
