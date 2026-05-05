"""Safety check — runs tests against the original program to verify they pass."""

import shutil
import subprocess
import tempfile
from pathlib import Path

from src import config
from src.mt_eval.execution.kill_checker import _extract_test_methods


def run_safety_check(
    original: Path,
    test_file: Path,
    timeout: int = config.EXECUTION_TIMEOUT,
) -> bool:
    """Run dafny run --no-verify --allow-warnings on combined (original + tests).

    Builds a temporary file with original content + extracted test methods,
    then executes it in an isolated temp directory. Returns True if exit code is 0.

    Args:
        original: Path to the original .dfy program.
        test_file: Path to the generated test .dfy file (original + tests).
        timeout: Max seconds for subprocess execution.

    Returns:
        True if dafny run exits 0, False otherwise (including timeout/error).
    """
    # Extract test methods from the test file
    test_methods = _extract_test_methods(test_file, original)

    # Build combined content: original + test methods
    original_content = original.read_text().rstrip()
    combined = original_content + "\n\n" + test_methods + "\n"

    # Run in isolated temp dir to avoid compilation artifact collisions
    work_dir = tempfile.mkdtemp(prefix=f"safety_{original.stem}_")
    combined_path = Path(work_dir) / f"{original.stem}.safety.dfy"
    combined_path.write_text(combined)

    try:
        cmd = [
            str(config.DAFNY_BINARY),
            "test",
            "--no-verify",
            "--allow-warnings",
            str(combined_path),
        ]
        result = subprocess.run(cmd, capture_output=True, timeout=timeout, cwd=work_dir)
        return result.returncode == 0
    except (subprocess.TimeoutExpired, Exception):
        return False
    finally:
        shutil.rmtree(work_dir, ignore_errors=True)
