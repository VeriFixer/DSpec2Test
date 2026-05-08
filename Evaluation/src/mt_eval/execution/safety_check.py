"""Safety check — runs tests against the original program to verify they pass."""

import shutil
import subprocess
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path

from src import config
from src.mt_eval.execution.kill_checker import _extract_test_methods


@dataclass
class SafetyCheckResult:
    """Result of a safety check execution."""

    passed: bool
    command: str = ""
    stdout: str = ""
    stderr: str = ""
    error_message: str = ""
    safety_file: str = ""
    execution_time: float = 0.0  # seconds


def run_safety_check(
    original: Path,
    test_file: Path,
    artifacts_dir: Path | None = None,
    timeout: int = config.EXECUTION_TIMEOUT,
) -> SafetyCheckResult:
    """Run dafny test --no-verify --allow-warnings on combined (original + tests).

    Executes in a temp dir to avoid compilation artifact collisions, then copies
    the safety .dfy file to artifacts_dir for permanent inspection. The recorded
    command references the permanent artifact path.

    Args:
        original: Path to the original .dfy program.
        test_file: Path to the generated test .dfy file (original + tests).
        artifacts_dir: Directory to persist the safety .dfy file for debugging.
            If None, uses the directory containing test_file.
        timeout: Max seconds for subprocess execution.

    Returns:
        SafetyCheckResult with pass/fail status and diagnostic info.
    """
    # Extract test methods from the test file
    test_methods = _extract_test_methods(test_file, original)

    # Build combined content: original + test methods
    original_content = original.read_text().rstrip()
    combined = original_content + "\n\n" + test_methods + "\n"

    # Determine permanent artifact location
    persist_dir = artifacts_dir if artifacts_dir is not None else test_file.parent
    persist_dir.mkdir(parents=True, exist_ok=True)
    permanent_path = persist_dir / f"{original.stem}.safety.dfy"

    # Run in isolated temp dir to avoid compilation artifact collisions
    work_dir = tempfile.mkdtemp(prefix=f"safety_{original.stem}_")
    tmp_combined = Path(work_dir) / f"{original.stem}.safety.dfy"
    tmp_combined.write_text(combined)

    # Record command with the permanent path (for debugging/results)
    cmd_permanent = [
        str(config.DAFNY_BINARY),
        "test",
        "--no-verify",
        "--allow-warnings",
        "--cores", "1",
        f"--solver-option:O:memory_max_size={config.DAFNY_MAX_MEMORY_MB}",
        str(permanent_path),
    ]
    cmd_str = " ".join(cmd_permanent)

    # Actual execution uses the temp path
    cmd_exec = [
        str(config.DAFNY_BINARY),
        "test",
        "--no-verify",
        "--allow-warnings",
        "--cores", "1",
        f"--solver-option:O:memory_max_size={config.DAFNY_MAX_MEMORY_MB}",
        str(tmp_combined),
    ]

    start = time.monotonic()
    try:
        result = subprocess.run(cmd_exec, capture_output=True, text=True, timeout=timeout, cwd=work_dir)
        elapsed = time.monotonic() - start
        # Copy artifact to permanent location regardless of outcome
        permanent_path.write_text(combined)

        if result.returncode == 0:
            return SafetyCheckResult(passed=True, command=cmd_str, safety_file=str(permanent_path),
                                     execution_time=elapsed)
        return SafetyCheckResult(
            passed=False,
            command=cmd_str,
            stdout=result.stdout.strip() if result.stdout else "",
            stderr=result.stderr.strip() if result.stderr else "",
            error_message=f"exit code {result.returncode}",
            safety_file=str(permanent_path),
            execution_time=elapsed,
        )
    except subprocess.TimeoutExpired:
        elapsed = time.monotonic() - start
        permanent_path.write_text(combined)
        return SafetyCheckResult(
            passed=False, command=cmd_str, error_message="timeout",
            safety_file=str(permanent_path), execution_time=elapsed,
        )
    except Exception as e:
        elapsed = time.monotonic() - start
        permanent_path.write_text(combined)
        return SafetyCheckResult(
            passed=False, command=cmd_str, error_message=str(e),
            safety_file=str(permanent_path), execution_time=elapsed,
        )
    finally:
        shutil.rmtree(work_dir, ignore_errors=True)
