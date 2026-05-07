"""Verification filter — runs dafny verify on programs, filters by pass/fail.

Uses ParallelExecutor for parallel verification.
"""

import subprocess
from pathlib import Path

from src.config import VERIFY_TIMEOUT, DAFNY_BINARY
from src.mt_eval.execution.parallel_executor import run_parallel_or_seq


def verify_program(dafny_file: Path) -> bool:
    """Run `dafny verify --allow-warnings <file>`, return True if passes.

    Returns False on non-zero exit or timeout.
    """
    try:
        result = subprocess.run(
            [str(DAFNY_BINARY), "verify", "--allow-warnings", str(dafny_file)],
            timeout=VERIFY_TIMEOUT,
            capture_output=True,
        )
        return result.returncode == 0
    except subprocess.TimeoutExpired:
        return False

def type_checks_program(dafny_file: Path) -> bool:
    """Run `dafny verify --allow-warnings <file>`, return True if passes.

    Returns False on non-zero exit or timeout.
    """
    try:
        result = subprocess.run(
            [str(DAFNY_BINARY), "resolve", "--allow-warnings", str(dafny_file)],
            timeout=VERIFY_TIMEOUT,
            capture_output=True,
        )
        return result.returncode == 0
    except subprocess.TimeoutExpired:
        return False


def filter_verified(
    files: list[Path], parallel: bool = True
) -> tuple[list[Path], int, int]:
    """Filter files by dafny verification, return (passed, pass_count, fail_count).

    Uses run_parallel_or_seq from parallel_executor.
    """
    results: list[bool] = run_parallel_or_seq(
        files, verify_program, "Verifying programs", parallel=parallel
    )

    passed: list[Path] = []
    pass_count = 0
    fail_count = 0

    for file, ok in zip(files, results):
        if ok:
            passed.append(file)
            pass_count += 1
        else:
            fail_count += 1

    return passed, pass_count, fail_count
