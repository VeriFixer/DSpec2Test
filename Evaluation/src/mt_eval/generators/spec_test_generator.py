"""SpecTestGenerator — invokes `dafny generate-tests Spec` via subprocess."""

import subprocess
from pathlib import Path

from src.mt_eval.core.abstract import TestGenResult, TestGenerator
from src import config


def _extract_test_methods(raw_output: str) -> str:
    """Extract test methods from dafny generate-tests output.

    Captures everything starting from the first 'method {:test}' line,
    discarding any include directives or warnings that precede it.
    """
    lines = raw_output.splitlines(keepends=True)
    for i, line in enumerate(lines):
        if "{:test}" in line:
            return "".join(lines[i:]).strip()
    return ""


class SpecTestGenerator(TestGenerator):
    """Concrete test generator using Dafny's generate-tests command (Spec mode).

    Uses the SpecTestGenerator fork binary which supports the 'Spec' mode.
    Output: original file content + generated test methods appended at bottom.
    """

    def __init__(self, dafny_binary: Path | None = None, mode: str = "Spec",
                 test_count: int = 1, length_limit: int = 50, **kwargs):
        super().__init__(name="SpecTestGenerator", **kwargs)
        self.dafny_binary = dafny_binary or config.SPECTEST_DAFNY_BINARY
        self.mode = mode
        self.test_count = test_count
        self.length_limit = length_limit

    def generate_tests(self, dafny_file: Path, output_file: Path) -> TestGenResult:
        """Run dafny generate-tests Spec and return result.

        The output test file = original source + generated test methods at bottom.
        """
        cmd = [
            str(self.dafny_binary),
            "generate-tests",
            self.mode,
            str(dafny_file.resolve()),
            "--test-count",
            str(self.test_count),
            "--length-limit",
            str(self.length_limit),
            "--ignore-warnings",
        ]
        cmd_str = " ".join(cmd)
        try:
            result = subprocess.run(
                cmd,
                timeout=config.TESTGEN_TIMEOUT,
                capture_output=True,
                text=True,
            )
            if result.returncode == 0 and result.stdout.strip():
                test_methods = _extract_test_methods(result.stdout)
                if not test_methods:
                    return TestGenResult(
                        success=False,
                        test_file=None,
                        error_message="no test methods extracted from output",
                        command=cmd_str,
                    )
                # Build test file: original content + test methods appended
                original_content = dafny_file.read_text()
                combined = original_content.rstrip() + "\n\n" + test_methods + "\n"

                output_file.parent.mkdir(parents=True, exist_ok=True)
                output_file.write_text(combined)
                return TestGenResult(success=True, test_file=output_file, command=cmd_str)

            # Build informative error message
            err_msg = ""
            if result.stderr and result.stderr.strip():
                # Take first 3 lines of stderr for concise reporting
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
            )
        except subprocess.TimeoutExpired:
            return TestGenResult(
                success=False, test_file=None, error_message="timeout", command=cmd_str,
            )
        except Exception as e:
            return TestGenResult(
                success=False, test_file=None, error_message=str(e), command=cmd_str,
            )
