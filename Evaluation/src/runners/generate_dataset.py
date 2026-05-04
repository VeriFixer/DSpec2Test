"""Dataset generation runner — sample, verify, mutate, diff.

CLI entry point for generating a mutant dataset from DafnyBench.

Usage:
    python -m src.runners.generate_dataset [--n-mutants N] [--output-dir DIR] [--sequential]
"""

import argparse
import logging
import shutil
import sys
import time
from pathlib import Path

from src.config import EXTERNAL_ROOT, SAMPLE_COUNT
from src.mt_eval.core.mutation import apply_mutation, generate_diff
from src.mt_eval.core.sampler import sample_programs, DEFAULT_SEED
from src.mt_eval.core.verification import verify_program, filter_verified

logger = logging.getLogger(__name__)

DAFNYBENCH_DIR: Path = EXTERNAL_ROOT / "bench" / "dafnybench"


# --- ANSI Colors ---
class C:
    BOLD = "\033[1m"
    GREEN = "\033[32m"
    RED = "\033[31m"
    YELLOW = "\033[33m"
    CYAN = "\033[36m"
    DIM = "\033[2m"
    RESET = "\033[0m"


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse CLI arguments."""
    parser = argparse.ArgumentParser(
        description="Generate a mutant dataset from DafnyBench."
    )
    parser.add_argument(
        "--n-mutants",
        type=int,
        default=SAMPLE_COUNT,
        help=f"Number of mutants to generate (default: {SAMPLE_COUNT})",
    )
    parser.add_argument(
        "--output-dir",
        type=str,
        default=None,
        help="Output directory for the dataset",
    )
    parser.add_argument(
        "--sequential",
        action="store_true",
        default=False,
        help="Run in sequential mode with per-file debug info",
    )
    parser.add_argument(
        "--seed",
        type=int,
        default=DEFAULT_SEED,
        help=f"RNG seed for reproducible sampling (default: {DEFAULT_SEED})",
    )
    return parser.parse_args(argv)


def run_pipeline(n_mutants: int, output_dir: Path, sequential: bool, seed: int = DEFAULT_SEED) -> int:
    """Execute the dataset generation pipeline.

    Returns 0 on success, 1 on critical failure.
    """
    parallel = not sequential
    t_start = time.time()

    # --- Step 1: Sample programs ---
    if sequential:
        print(f"[generate_dataset] Sampling {n_mutants} programs from DafnyBench (seed={seed})...")
    logger.info("Sampling %d programs from %s (seed=%d)", n_mutants, DAFNYBENCH_DIR, seed)

    sampled = sample_programs(DAFNYBENCH_DIR, n_mutants, seed=seed)
    if not sampled:
        logger.error("No programs sampled — aborting.")
        return 1

    if sequential:
        print(f"[generate_dataset] Sampled {len(sampled)} programs")

    # --- Step 2: Filter verified originals ---
    if sequential:
        print("[generate_dataset] Verifying originals...")
    logger.info("Verifying %d originals", len(sampled))

    verified, pass_count, fail_count = filter_verified(sampled, parallel=parallel)

    if sequential:
        print(
            f"[generate_dataset] Verification: {pass_count} passed, {fail_count} failed"
        )
    logger.info("Verification: %d passed, %d failed", pass_count, fail_count)

    if not verified:
        logger.error("No programs passed verification — aborting.")
        return 1

    # --- Step 3: Prepare output dirs ---
    original_dir = output_dir / "original"
    killed_dir = output_dir / "killed"
    original_dir.mkdir(parents=True, exist_ok=True)
    killed_dir.mkdir(parents=True, exist_ok=True)

    # --- Step 4: Mutate and verify mutants (parallel or sequential) ---
    def _mutate_and_check(orig_file: Path) -> tuple[Path, Path | None]:
        """Apply mutation and verify mutant fails. Returns (orig, mutant_path|None)."""
        stem = orig_file.stem
        mutant_work_dir = output_dir / "_tmp_mutants" / stem
        mutant_path = apply_mutation(orig_file, mutant_work_dir)

        if mutant_path is None:
            logger.warning("Mutation failed for %s", orig_file.name)
            return (orig_file, None)

        # Verify mutant FAILS (confirms it's actually buggy)
        if verify_program(mutant_path):
            logger.info("Mutant still verifies for %s — not a real bug", orig_file.name)
            return (orig_file, None)

        return (orig_file, mutant_path)

    from src.mt_eval.execution.parallel_executor import run_parallel_or_seq

    mutation_results: list[tuple[Path, Path | None]] = run_parallel_or_seq(
        verified, _mutate_and_check, "Mutating & checking", parallel=parallel
    )

    # --- Step 5: Collect valid mutants ---
    valid_count = 0
    skip_count = 0
    mutation_failed = 0
    still_verifies = 0
    generated_paths: list[Path] = []

    for orig_file, mutant_path in mutation_results:
        if mutant_path is None:
            skip_count += 1
            if sequential:
                print(f"[generate_dataset]   Skipped {orig_file.name}")
            continue

        if sequential:
            print(f"[generate_dataset]   Mutant confirmed buggy for {orig_file.name}")

        # Copy original
        shutil.copy2(orig_file, original_dir / orig_file.name)

        # Copy mutant
        mutant_dest = killed_dir / mutant_path.name
        shutil.copy2(mutant_path, mutant_dest)

        # Generate diff
        diff_path = killed_dir / (mutant_path.stem + ".txt")
        generate_diff(orig_file, mutant_path, diff_path)

        generated_paths.append(mutant_dest)
        valid_count += 1

    # --- Step 6: Cleanup temp dir ---
    tmp_mutants = output_dir / "_tmp_mutants"
    if tmp_mutants.exists():
        shutil.rmtree(tmp_mutants)

    t_elapsed = time.time() - t_start

    # --- Step 7: Summary ---
    _print_summary(
        n_sampled=len(sampled),
        n_verified=len(verified),
        n_failed_verify=fail_count,
        n_valid_mutants=valid_count,
        n_skipped=skip_count,
        generated_paths=generated_paths,
        output_dir=output_dir,
        elapsed=t_elapsed,
        seed=seed,
    )

    logger.info("Dataset complete: %d valid, %d skipped", valid_count, skip_count)

    if valid_count == 0:
        logger.error("No valid mutants produced — aborting.")
        return 1

    return 0


def _print_summary(
    n_sampled: int,
    n_verified: int,
    n_failed_verify: int,
    n_valid_mutants: int,
    n_skipped: int,
    generated_paths: list[Path],
    output_dir: Path,
    elapsed: float,
    seed: int,
) -> None:
    """Print colored summary to stdout."""
    mins, secs = divmod(int(elapsed), 60)

    print()
    print(f"{C.BOLD}{'═' * 60}{C.RESET}")
    print(f"{C.BOLD}{C.CYAN}  DATASET GENERATION SUMMARY{C.RESET}")
    print(f"{C.BOLD}{'═' * 60}{C.RESET}")
    print()
    print(f"  {C.BOLD}Sampling{C.RESET}")
    print(f"    Programs sampled:      {C.CYAN}{n_sampled}{C.RESET}")
    print(f"    Seed:                  {C.DIM}{seed}{C.RESET}")
    print()
    print(f"  {C.BOLD}Verification (originals){C.RESET}")
    print(f"    Passed:                {C.GREEN}{n_verified}{C.RESET}")
    print(f"    Failed:                {C.RED}{n_failed_verify}{C.RESET}")
    print()
    print(f"  {C.BOLD}Mutation{C.RESET}")
    print(f"    Valid mutants:         {C.GREEN}{n_valid_mutants}{C.RESET}")
    print(f"    Skipped:               {C.YELLOW}{n_skipped}{C.RESET}")
    yield_pct = (n_valid_mutants / n_verified * 100) if n_verified else 0
    print(f"    Yield:                 {C.BOLD}{yield_pct:.1f}%{C.RESET}")
    print()
    print(f"  {C.BOLD}Output{C.RESET}")
    print(f"    Directory:             {C.DIM}{output_dir}{C.RESET}")
    print(f"    Time:                  {mins}m {secs}s")
    print()

    if generated_paths:
        print(f"  {C.BOLD}Generated mutants:{C.RESET}")
        for p in generated_paths:
            print(f"    {C.GREEN}✓{C.RESET} {p}")
    else:
        print(f"  {C.RED}No mutants generated.{C.RESET}")

    print()
    print(f"{C.BOLD}{'═' * 60}{C.RESET}")
    print()


def main(argv: list[str] | None = None) -> None:
    """Entry point."""
    args = parse_args(argv)

    output_dir = Path(args.output_dir) if args.output_dir else Path("dataset_output")

    exit_code = run_pipeline(
        n_mutants=args.n_mutants,
        output_dir=output_dir,
        sequential=args.sequential,
        seed=args.seed,
    )
    sys.exit(exit_code)


if __name__ == "__main__":
    main()
