"""KillChecker — runs a test file against a mutant via dafny run --no-verify."""

import re
import subprocess
import time
from pathlib import Path

from src import config
from src.mt_eval.core.models import MutantResult, MutantStatus


def _derive_original_name(mutant_name: str) -> str:
    """Derive original filename from mutant name.

    Mutant naming convention: <original_stem>__<line_range>_<mutation_type>.dfy
    Returns '<original_stem>.dfy'. Falls back to mutant_name if no '__' found.
    """
    stem = Path(mutant_name).stem  # strip .dfy
    if "__" in stem:
        original_stem = stem.split("__")[0]
        return f"{original_stem}.dfy"
    return mutant_name


def _extract_test_methods(test_file: Path, original_file: Path) -> str:
    """Extract only the test methods from a test file.

    The test file = original content + test methods at bottom.
    We strip the original content prefix to get just the tests.
    """
    test_content = test_file.read_text()
    original_content = original_file.read_text().rstrip()

    # If test file starts with original content, strip it
    if test_content.startswith(original_content):
        return test_content[len(original_content):].strip()

    # Fallback: extract method {:test} blocks
    # Find first occurrence of "method {:test}"
    match = re.search(r'^method\s+\{:test\}', test_content, re.MULTILINE)
    if match:
        return test_content[match.start():].strip()

    # Last resort: return everything after the original file length
    return test_content.strip()


class KillChecker:
    """Runs a test suite against a mutant and determines kill status."""

    def __init__(self, timeout: int = config.EXECUTION_TIMEOUT) -> None:
        self.timeout = timeout
        self.dafny_binary = config.DAFNY_BINARY

    def check_kill(self, test_file: Path, mutant_file: Path) -> MutantResult:
        """Build combined file (mutant + tests) and run via 'dafny run --no-verify'.

        Creates a file in kill_tests/ dir (sibling to tests/) containing
        the mutant source + test methods. This file is kept for debugging.

        Args:
            test_file: Path to the generated test .dfy file (original + tests).
            mutant_file: Path to the mutant .dfy file.

        Returns:
            MutantResult with status KILLED/SURVIVED/TIMEOUT/ERROR.
        """
        mutant_name = mutant_file.name
        original_name = _derive_original_name(mutant_name)

        # Derive original file path from test_file's sibling original/ dir
        dataset_dir = test_file.parent.parent  # tests/ -> dataset dir
        original_file = dataset_dir / "original" / original_name

        # Extract test methods from the test file
        test_methods = _extract_test_methods(test_file, original_file)

        # Build combined file: mutant content + test methods
        kill_tests_dir = dataset_dir / "kill_tests"
        kill_tests_dir.mkdir(parents=True, exist_ok=True)

        mutant_content = mutant_file.read_text().rstrip()
        combined = mutant_content + "\n\n" + test_methods + "\n"

        combined_file = kill_tests_dir / f"{mutant_file.stem}.test.dfy"
        combined_file.write_text(combined)

        cmd = [str(self.dafny_binary), "run", "--no-verify", str(combined_file)]
        start = time.monotonic()

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                timeout=self.timeout,
            )
            elapsed = time.monotonic() - start

            if result.returncode != 0:
                status = MutantStatus.KILLED
            else:
                status = MutantStatus.SURVIVED

        except subprocess.TimeoutExpired:
            elapsed = time.monotonic() - start
            status = MutantStatus.TIMEOUT

        except Exception:
            elapsed = time.monotonic() - start
            status = MutantStatus.ERROR

        return MutantResult(
            mutant_name=mutant_name,
            original_name=original_name,
            status=status,
            execution_time=elapsed,
            kill_check_command=" ".join(cmd),
        )
