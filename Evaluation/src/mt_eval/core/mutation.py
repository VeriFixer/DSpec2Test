"""Mutation runner — invokes MutDafny plugin via Dafny and generates diffs.

MutDafny is a Dafny compiler plugin. It works in two passes:
1. Scan: `dafny verify <file> --plugin mutdafny.dll,scan` → produces targets.csv
2. Mutate: For each target, `dafny verify <file> --plugin mutdafny.dll,"mut <pos> <op> [arg]"`
   → produces mutant .dfy files in the working directory.

apply_mutation: runs MutDafny on a Dafny file, returns list of mutant paths.
generate_diff: produces unified diff between original and mutant files.
"""

import csv
import difflib
import logging
import subprocess
import tempfile
import time
import re
from pathlib import Path

from src.config import MUTDAFNY_PLUGIN, MUTDAFNY_DIR, MUTDAFNY_DAFNY_BINARY, DAFNY_MAX_MEMORY_MB
from src.mt_eval.core.verification import verify_program, type_checks_program

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
        "--cores", "1",
        f"--solver-option:O:memory_max_size={DAFNY_MAX_MEMORY_MB}",
        f"--plugin:{MUTDAFNY_PLUGIN},{plugin_arg}",
    ]

    start = time.monotonic()
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            cwd=str(cwd),
        )
        elapsed = time.monotonic() - start
        logger.info("[mutdafny] %s arg=%s — %.1fs (rc=%d)",
                    dafny_file.name, plugin_arg, elapsed, result.returncode)
        if result.returncode != 0:
            cmd_str = " ".join(cmd)
            stderr_snippet = (result.stderr or "").strip().splitlines()[:5]
            logger.warning("[mutdafny] FAILED cmd: %s\n  stderr: %s",
                           cmd_str, "\n  ".join(stderr_snippet))
        return result
    except (subprocess.TimeoutExpired, OSError) as exc:
        elapsed = time.monotonic() - start
        logger.warning("Dafny plugin call failed for %s (arg=%s): %s [%.1fs]",
                       dafny_file, plugin_arg, exc, elapsed)
        return None

import re

def apply_mutation(original_file: Path, output_dir: Path, num_mutants: int = 1) -> list[Path]:
    """Invoke MutDafny on original_file, return exactly num_mutants mutant paths.

    Uses the two-pass approach:
    1. Scan for mutation targets → targets.csv
    2. Apply mutations → mutant .dfy files

    Args:
        original_file: Path to the original .dfy source file.
        output_dir: Directory where mutant files will be collected.
        num_mutants: Exact number of mutants to generate per file (unless impossible).

    Returns:
        List of paths to mutant files (may be empty on failure).
    """
    output_dir.mkdir(parents=True, exist_ok=True)
    collected: list[Path] = []

    # Use a temp working directory for MutDafny's intermediate files
    with tempfile.TemporaryDirectory() as work_dir:
        work_path = Path(work_dir)

        # Pass 1: Scan for mutation targets
        result = _run_dafny_plugin(original_file, "scan", cwd=work_path)
        if result is None:
            return []

        targets_file = work_path / "targets.csv"
        if not targets_file.exists():
            logger.warning("MutDafny scan produced no targets.csv for %s", original_file)
            return []

        # Parse targets.csv
        targets = []
        with open(targets_file, "r") as f:
            reader = csv.reader(f)
            for row in reader:
                if row:
                    targets.append(row)

        if not targets:
            logger.warning("MutDafny produced empty targets for %s", original_file)
            return []

        # Pass 2: Apply mutations until we have num_mutants
        for target in targets:
            if len(collected) >= num_mutants:
                break

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
            for mf in mutant_files:
                if len(collected) >= num_mutants:
                    break
                if type_checks_program(mf) and not verify_program(mf):
                    dest = output_dir / mf.name
                    dest.write_text(mf.read_text())
                    collected.append(dest)

            # Clean up generated files for next iteration
            for mf in work_path.glob("*.dfy"):
                mf.unlink()

            # Clean up any elapsed-time.csv
            elapsed = work_path / "elapsed-time.csv"
            if elapsed.exists():
                elapsed.unlink()

    if not collected:
        logger.warning("MutDafny produced no mutants for %s", original_file)

    return collected


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


def get_formatted_original_lines(original_file: Path, formatted_dir: Path) -> list[str]:
    """
    Parses the original file and prints it using Dafny's AST printer.
    This automatically strips comments and perfectly aligns spacing with MutDafny.
    """
    formatted_dir.mkdir(parents=True, exist_ok=True)
    output_path = formatted_dir / original_file.name

    cmd = [
        str(MUTDAFNY_DAFNY_BINARY), 
        "resolve", 
        str(original_file), 
        "--print", 
        str(output_path)
    ]
    
    subprocess.run(cmd, capture_output=True, text=True)

    formatted_code = output_path.read_text()
    
    return formatted_code.splitlines()

def get_mutant_diff_lines(original_lines: list[str], mutant_file: Path) -> list[int]:
    """Compares original lines against the mutant file and returns 
    a sorted list of line numbers (1-indexed) where differences exist."""
    mutant_lines = mutant_file.read_text().splitlines()
    matcher = difflib.SequenceMatcher(None, original_lines, mutant_lines)
    
    changed_lines = set()
    
    for tag, i1, i2, j1, j2 in matcher.get_opcodes():
        if tag != 'equal':
            if tag == 'delete':
                changed_lines.add(max(1, j1 if j1 > 0 else 1))
            else:
                for j in range(j1, j2):
                    changed_lines.add(j + 1)
                    
    return sorted(list(changed_lines))