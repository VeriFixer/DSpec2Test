"""Mutant generation runner — collect programs, generate & filter mutants.

CLI entry point for generating mutants from the fixed program set
in dataset/selected_programs/.

Usage:
    python -m src.runners.generate_mutants [--n-mutants-per-program N] [--sequential]
"""

import argparse
import logging
import sys
from pathlib import Path

from src.config import SELECTED_PROGRAMS_DIR, SELECTED_PROGRAMS_MUTANTS_DIR
from src.mt_eval.core.mutation import apply_mutation
from src.mt_eval.core.verification import verify_program
from src.mt_eval.execution.parallel_executor import run_parallel_or_seq

logger = logging.getLogger(__name__)


def collect_programs(programs_dir: Path) -> list[Path]:
    """Return sorted list of .dfy files from programs_dir.

    Exits with code 1 if no .dfy files found.
    """
    programs = sorted(programs_dir.glob("*.dfy"))
    if not programs:
        logger.error("No .dfy files found in %s", programs_dir)
        sys.exit(1)
    return programs


def _process_program(
    program: Path, output_dir: Path, max_mutants: int
) -> tuple[str, list[Path]]:
    """Generate and filter mutants for a single program.

    Returns (program_stem, list_of_valid_mutant_paths).
    """
    stem = program.stem
    prog_output_dir = output_dir / stem

    # Generate mutants via MutDafny
    mutants = apply_mutation(program, prog_output_dir, max_mutants=max_mutants)

    # Filter: keep only mutants that FAIL verification (real bugs)
    valid_mutants = [m for m in mutants if not verify_program(m)]

    if not valid_mutants:
        logger.warning("No valid mutants produced for %s", program.name)

    return stem, valid_mutants


def generate_mutants(
    programs: list[Path],
    output_dir: Path,
    max_mutants: int,
    parallel: bool,
) -> dict[str, list[Path]]:
    """For each program, call apply_mutation + verify filter.

    Returns: {original_stem: [mutant_paths]} mapping.
    Mutants that pass dafny verify are discarded (not real bugs).
    """
    output_dir.mkdir(parents=True, exist_ok=True)

    def process(program: Path) -> tuple[str, list[Path]]:
        return _process_program(program, output_dir, max_mutants)

    results: list[tuple[str, list[Path]]] = run_parallel_or_seq(
        programs, process, "Generating mutants", parallel=parallel
    )

    return dict(results)


def parse_args(argv=None):
    """Parse CLI arguments for mutant generation."""
    parser = argparse.ArgumentParser(
        description="Generate mutants from selected programs."
    )
    parser.add_argument(
        "--n-mutants-per-program",
        type=int,
        default=10,
        help="Max mutants to generate per program (default: 10)",
    )
    parser.add_argument(
        "--sequential",
        action="store_true",
        default=False,
        help="Run sequentially instead of in parallel",
    )
    return parser.parse_args(argv)


def run_mutant_generation(
    n_mutants_per_program: int = 10, sequential: bool = False
) -> int:
    """Collect programs, generate mutants, filter, write. Returns 0 on success."""
    programs = collect_programs(SELECTED_PROGRAMS_DIR)
    logger.info(
        "Collected %d programs from %s", len(programs), SELECTED_PROGRAMS_DIR
    )

    results = generate_mutants(
        programs,
        SELECTED_PROGRAMS_MUTANTS_DIR,
        max_mutants=n_mutants_per_program,
        parallel=not sequential,
    )

    total_mutants = sum(len(v) for v in results.values())
    logger.info(
        "Generated %d mutants across %d programs", total_mutants, len(results)
    )
    return 0


def main(argv=None):
    """CLI entry point."""
    args = parse_args(argv)
    rc = run_mutant_generation(
        n_mutants_per_program=args.n_mutants_per_program,
        sequential=args.sequential,
    )
    sys.exit(rc)


if __name__ == "__main__":
    main()
