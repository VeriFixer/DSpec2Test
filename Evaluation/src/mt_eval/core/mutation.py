"""Mutation runner — invokes MutDafny plugin via Dafny and generates diffs.

MutDafny is a Dafny compiler plugin. It works in two passes:
1. Scan: `dafny verify <file> --plugin mutdafny.dll,scan` → produces targets.csv
2. Mutate: For each target, `dafny verify <file> --plugin mutdafny.dll,"mut <pos> <op> [arg]"`
   → produces mutant .dfy files in the working directory.

apply_mutation: runs MutDafny on a Dafny file, returns first mutant path or None.
generate_diff: produces unified diff between original and mutant files.
"""

import csv
import difflib
import logging
import subprocess
import tempfile
from pathlib import Path

from src.config import MUTDAFNY_PLUGIN, MUTDAFNY_DIR, MUTDAFNY_DAFNY_BINARY

logger = logging.getLogger(__name__)


def _run_dafny_plugin(dafny_file: Path, plugin_arg: str, cwd: Path,
                      timeout: int = 300) -> subprocess.CompletedProcess | None:
    """Run dafny verify with mutdafny plugin argument.

    Args:
        dafny_file: Path to .dfy file.
        plugin_arg: Plugin argument string (e.g. "scan" or "mut 3 BinaryOp").
        cwd: Working directory for the subprocess.
        timeout: Timeout in seconds.

    Returns:
        CompletedProcess on success, None on failure.
    """
    cmd = [
        str(MUTDAFNY_DAFNY_BINARY), "verify", str(dafny_file),
        "--allow-warnings",
        f"--plugin:{MUTDAFNY_PLUGIN},{plugin_arg}",
    ]

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(cwd),
        )
        return result
    except (subprocess.TimeoutExpired, OSError) as exc:
        logger.warning("Dafny plugin call failed for %s (arg=%s): %s",
                       dafny_file, plugin_arg, exc)
        return None


def apply_mutation(original_file: Path, output_dir: Path) -> Path | None:
    """Invoke MutDafny on original_file, return first mutant path or None on failure.

    Uses the two-pass approach:
    1. Scan for mutation targets → targets.csv
    2. Apply first available mutation → mutant .dfy file

    Args:
        original_file: Path to the original .dfy source file.
        output_dir: Directory where mutant files will be collected.

    Returns:
        Path to first mutant file, or None on failure.
    """
    output_dir.mkdir(parents=True, exist_ok=True)

    # Use a temp working directory for MutDafny's intermediate files
    with tempfile.TemporaryDirectory() as work_dir:
        work_path = Path(work_dir)

        # Pass 1: Scan for mutation targets
        result = _run_dafny_plugin(original_file, "scan", cwd=work_path)
        if result is None:
            return None

        targets_file = work_path / "targets.csv"
        if not targets_file.exists():
            logger.warning("MutDafny scan produced no targets.csv for %s", original_file)
            return None

        # Parse targets.csv
        targets = []
        with open(targets_file, "r") as f:
            reader = csv.reader(f)
            for row in reader:
                if row:
                    targets.append(row)

        if not targets:
            logger.warning("MutDafny produced empty targets for %s", original_file)
            return None

        # Pass 2: Apply first mutation that produces a valid mutant
        for target in targets:
            pos = target[0].strip()
            op = target[1].strip() if len(target) > 1 else ""
            arg = target[2].strip() if len(target) > 2 else ""

            if arg:
                plugin_arg = f"mut {pos} {op} {arg}"
            else:
                plugin_arg = f"mut {pos} {op}"

            mut_result = _run_dafny_plugin(original_file, plugin_arg, cwd=work_path)
            if mut_result is None:
                continue

            # MutDafny writes .dfy files in the working directory
            mutant_files = sorted(work_path.glob("*.dfy"))
            if mutant_files:
                # Move first mutant to output_dir
                first_mutant = mutant_files[0]
                dest = output_dir / first_mutant.name
                dest.write_text(first_mutant.read_text())
                # Clean up generated files for next iteration
                for mf in mutant_files:
                    mf.unlink()
                return dest

            # Clean up any elapsed-time.csv
            elapsed = work_path / "elapsed-time.csv"
            if elapsed.exists():
                elapsed.unlink()

    logger.warning("MutDafny produced no mutants for %s", original_file)
    return None


def generate_diff(original: Path, mutant: Path, output_path: Path) -> Path:
    """Produce a unified diff file between original and mutant.

    Args:
        original: Path to original .dfy file.
        mutant: Path to mutant .dfy file.
        output_path: Where to write the diff.

    Returns:
        output_path after writing.
    """
    original_lines = original.read_text().splitlines(keepends=True)
    mutant_lines = mutant.read_text().splitlines(keepends=True)

    diff = difflib.unified_diff(
        original_lines,
        mutant_lines,
        fromfile=str(original),
        tofile=str(mutant),
    )

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text("".join(diff))
    return output_path
