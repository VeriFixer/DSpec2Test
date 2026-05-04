"""KillChecker — runs a test file against a mutant via dafny run --no-verify."""

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


class KillChecker:
    """Runs a test suite against a mutant and determines kill status."""

    def __init__(self, timeout: int = config.EXECUTION_TIMEOUT) -> None:
        self.timeout = timeout
        self.dafny_binary = config.DAFNY_BINARY

    def check_kill(self, test_file: Path, mutant_file: Path) -> MutantResult:
        """Run test_file against mutant_file via 'dafny run --no-verify'.

        Args:
            test_file: Path to the generated test .dfy file.
            mutant_file: Path to the mutant .dfy file.

        Returns:
            MutantResult with status KILLED/SURVIVED/TIMEOUT/ERROR.
        """
        mutant_name = mutant_file.name
        original_name = _derive_original_name(mutant_name)
        start = time.monotonic()

        try:
            result = subprocess.run(
                [str(self.dafny_binary), "run", "--no-verify", str(test_file)],
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
        )
