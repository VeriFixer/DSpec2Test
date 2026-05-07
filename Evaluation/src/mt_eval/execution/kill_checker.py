"""KillChecker — runs a test file against a mutant via dafny run --no-verify."""

import re
import shutil
import subprocess
import tempfile
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
        original_stem = stem.rsplit("__", 1)[0]
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

    def __init__(
        self,
        timeout: int = config.EXECUTION_TIMEOUT,
        output_dir: Path | None = None,
        originals_dir: Path | None = None,
    ) -> None:
        self.timeout = timeout
        self.dafny_binary = config.DAFNY_BINARY
        self.output_dir = output_dir
        self.originals_dir = originals_dir

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

        # Derive original file path
        if self.originals_dir is not None:
            original_file = self.originals_dir / original_name
        else:
            dataset_dir = test_file.parent.parent  # tests/ -> dataset dir
            original_file = dataset_dir / "original" / original_name

        # Extract test methods from the test file
        test_methods = _extract_test_methods(test_file, original_file)

        # Build combined file: mutant content + test methods
        if self.output_dir is not None:
            kill_tests_dir = self.output_dir
        else:
            fallback_dir = test_file.parent.parent  # tests/ -> dataset dir
            kill_tests_dir = fallback_dir / "kill_tests"
        kill_tests_dir.mkdir(parents=True, exist_ok=True)

        mutant_content = mutant_file.read_text().rstrip()
        combined = mutant_content + "\n\n" + test_methods + "\n"

        combined_file = kill_tests_dir / f"{mutant_file.stem}.test.dfy"
        combined_file.write_text(combined)

        # Run dafny in a per-mutant temp dir to isolate compilation artifacts
        work_dir = tempfile.mkdtemp(prefix=f"kill_{mutant_file.stem}_")
        work_dfy = Path(work_dir) / combined_file.name
        work_dfy.write_text(combined)

        cmd = [str(self.dafny_binary), "test", "--no-verify", "--allow-warnings", str(work_dfy)]
        # For reporting, show the persistent path (not the temp one)
        report_cmd = [str(self.dafny_binary), "test", "--no-verify", "--allow-warnings", str(combined_file)]
        start = time.monotonic()

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=self.timeout,
                cwd=work_dir,
            )
            elapsed = time.monotonic() - start
            stdout = result.stdout or ""
            stderr = result.stderr or ""

            if result.returncode != 0:
                status = MutantStatus.KILLED
            else:
                status = MutantStatus.SURVIVED

        except subprocess.TimeoutExpired:
            elapsed = time.monotonic() - start
            stdout = ""
            stderr = "TIMEOUT"
            status = MutantStatus.TIMEOUT

        except Exception as e:
            elapsed = time.monotonic() - start
            stdout = ""
            stderr = str(e)
            status = MutantStatus.ERROR

        finally:
            shutil.rmtree(work_dir, ignore_errors=True)

        return MutantResult(
            mutant_name=mutant_name,
            original_name=original_name,
            status=status,
            execution_time=elapsed,
            kill_check_command=" ".join(report_cmd),
            stdout=stdout.strip(),
            stderr=stderr.strip(),
        )
