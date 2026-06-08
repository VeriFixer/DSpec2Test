"""Mutant generation runner — collect programs, generate & filter mutants.

CLI entry point for generating mutants from the fixed program set
in dataset/selected_programs/.

Usage:
    python -m src.runners.generate_mutants [--n-mutants-per-program N] [--sequential]
"""

import argparse
import logging
import sys
import time
import json
from pathlib import Path

from src.logging_config import get_logger
from src.config import SELECTED_PROGRAMS_DIR, SELECTED_PROGRAMS_MUTANTS_DIR, SELECTED_PROGRAMS_FORMATTED_DIR, DATASET_ROOT
from src.mt_eval.core.mutation import apply_mutation, get_formatted_original_lines, get_mutant_diff_lines
from src.mt_eval.execution.parallel_executor import run_parallel_or_seq

logger = get_logger(__name__)


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
    program: Path, output_dir: Path, num_mutants: int
) -> tuple[str, list[Path]]:
    """Generate and filter mutants for a single program.

    Returns (program_stem, list_of_valid_mutant_paths).
    """
    stem = program.stem
    prog_output_dir = output_dir / stem
    diff_mapping = {}

    start = time.monotonic()

    # Generate mutants via MutDafny
    mutants = apply_mutation(program, prog_output_dir, num_mutants=num_mutants)

    mutation_time = time.monotonic() - start

    if mutants:
        original_lines = get_formatted_original_lines(program, SELECTED_PROGRAMS_FORMATTED_DIR)

        for mutant_path in mutants:
            diff_lines = get_mutant_diff_lines(original_lines, mutant_path)
            diff_mapping[mutant_path.name] = diff_lines

    logger.info(
        "[generate_mutants] %s — %.1fs total "
        "| %d generated",
        program.name, mutation_time,
        len(mutants)
    )

    if not mutants:
        logger.warning("No valid mutants produced for %s", program.name)

    return stem, mutants, diff_mapping


def generate_mutants(
    programs: list[Path],
    output_dir: Path,
    num_mutants: int,
    parallel: bool,
) -> dict[str, list[Path]]:
    """For each program, call apply_mutation + verify filter.

    Returns: {original_stem: [mutant_paths]} mapping.
    Mutants that pass dafny verify are discarded (not real bugs).
    """
    output_dir.mkdir(parents=True, exist_ok=True)

    def process(program: Path) -> tuple[str, list[Path]]:
        return _process_program(program, output_dir, num_mutants)

    results: list[tuple[str, list[Path]]] = run_parallel_or_seq(
        programs, process, "Generating mutants", parallel=parallel
    )

    mutants_dict = {res[0]: res[1] for res in results}
    
    diff_mapping = {}
    for res in results:
        diff_mapping.update(res[2])

    return mutants_dict, diff_mapping


def store_diff_json(diff_mapping, json_file):
    
    DATASET_ROOT.mkdir(parents=True, exist_ok=True)
    json_path = DATASET_ROOT / json_file
    
    with open(json_path, 'w', encoding='utf-8') as f:
            json.dump(diff_mapping, f, indent=4)
        
    logger.info(f"Diff lines mapping saved to {json_path.name}")


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
    parser.add_argument(
        "--json-file", 
        default="ground_truth.json",
        help="JSON file to output the diff to (default: ground_truth.json)."
    )
    return parser.parse_args(argv)


def run_mutant_generation(
    n_mutants_per_program: int = 10, sequential: bool = False, json_file="ground_truth.json"
) -> int:
    """Collect programs, generate mutants, filter, write. Returns 0 on success."""
    programs = collect_programs(SELECTED_PROGRAMS_DIR)
    logger.info(
        "Collected %d programs from %s", len(programs), SELECTED_PROGRAMS_DIR
    )

    results, diff_mapping = generate_mutants(
        programs,
        SELECTED_PROGRAMS_MUTANTS_DIR,
        num_mutants=n_mutants_per_program,
        parallel=not sequential,
    )

    store_diff_json(diff_mapping, json_file)

    return 0


def main(argv=None):
    """CLI entry point."""
    start_time = time.time()

    args = parse_args(argv)
    rc = run_mutant_generation(
        n_mutants_per_program=args.n_mutants_per_program,
        sequential=args.sequential,
        json_file=args.json_file
    )

    end_time = time.time()
    elapsed_time = end_time - start_time
    logger.info(f"Total mutant generation time: {elapsed_time:.4f} seconds")

    sys.exit(rc)


if __name__ == "__main__":
    main()
