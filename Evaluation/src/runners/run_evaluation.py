"""Evaluation runner — generate tests, kill check, compute metrics, report.

CLI entry point for running mutation kill evaluation on a dataset.

Usage:
    python -m src.runners.run_evaluation DATASET_PATH [--clean-cache] [--sequential] [--output-dir DIR]
"""

import argparse
import logging
import shutil
import sys
from pathlib import Path

from src.mt_eval.core.models import MutantResult
from src.mt_eval.execution.kill_checker import KillChecker
from src.mt_eval.execution.parallel_executor import run_parallel_or_seq
from src.mt_eval.generators.spec_test_generator import SpecTestGenerator
from src.mt_eval.metrics.kill_rate import compute_kill_rate
from src.mt_eval.reporting.summary import print_summary, write_json_results

logger = logging.getLogger(__name__)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse CLI arguments."""
    parser = argparse.ArgumentParser(
        description="Run mutation kill evaluation on a dataset."
    )
    parser.add_argument(
        "dataset_path",
        type=str,
        help="Path to dataset directory (must contain original/ and killed/ subdirs)",
    )
    parser.add_argument(
        "--clean-cache",
        action="store_true",
        default=False,
        help="Remove tests/ subdir and previous results before running",
    )
    parser.add_argument(
        "--sequential",
        action="store_true",
        default=False,
        help="Disable parallel execution; print per-mutant debug info",
    )
    parser.add_argument(
        "--output-dir",
        type=str,
        default=None,
        help="Directory for results JSON (default: dataset_path)",
    )
    return parser.parse_args(argv)


def _validate_dataset(dataset_path: Path) -> bool:
    """Check dataset_path has original/ and killed/ subdirs."""
    original_dir = dataset_path / "original"
    killed_dir = dataset_path / "killed"
    if not original_dir.is_dir():
        logger.error("Missing original/ subdirectory in %s", dataset_path)
        return False
    if not killed_dir.is_dir():
        logger.error("Missing killed/ subdirectory in %s", dataset_path)
        return False
    return True


def _derive_original_stem(mutant_name: str) -> str:
    """Extract original stem from mutant filename.

    Convention: <original_stem>__<line_range>_<mutation_type>.dfy
    """
    stem = Path(mutant_name).stem
    if "__" in stem:
        return stem.split("__")[0]
    return stem


def run_pipeline(dataset_path: Path, *, clean_cache: bool, sequential: bool, output_dir: Path) -> int:
    """Execute the evaluation pipeline.

    Returns 0 on success, 1 on critical failure.
    """
    # --- Validate dataset ---
    if not dataset_path.is_dir():
        logger.error("Dataset path does not exist: %s", dataset_path)
        return 1

    if not _validate_dataset(dataset_path):
        return 1

    original_dir = dataset_path / "original"
    killed_dir = dataset_path / "killed"
    tests_dir = dataset_path / "tests"

    # --- Clean cache if requested ---
    if clean_cache:
        if tests_dir.exists():
            if sequential:
                print("[run_evaluation] Cleaning tests/ cache...")
            shutil.rmtree(tests_dir)
        # Remove previous results JSON
        for json_file in output_dir.glob("results_*.json"):
            json_file.unlink()

    tests_dir.mkdir(parents=True, exist_ok=True)

    # --- Step 1: Generate tests for each original ---
    originals = sorted(original_dir.glob("*.dfy"))
    if not originals:
        logger.error("No .dfy files found in original/")
        return 1

    if sequential:
        print(f"[run_evaluation] Found {len(originals)} original programs")

    generator = SpecTestGenerator()
    test_map: dict[str, Path] = {}  # original_stem -> test_file
    test_gen_cmd_map: dict[str, str] = {}  # original_stem -> command used

    def _generate_test_task(orig: Path) -> tuple[str, Path | None, str | None, str]:
        test_file = tests_dir / f"{orig.stem}.test.dfy"
        result = generator.generate_tests(orig, test_file)
        if result.success and result.test_file:
            return (orig.stem, result.test_file, None, result.command)
        return (orig.stem, None, result.error_message, result.command)

    parallel = not sequential
    gen_results: list[tuple[str, Path | None, str | None, str]] = run_parallel_or_seq(
        originals,
        _generate_test_task,
        "Test generation",
        parallel=parallel,
    )

    for stem, test_file, error_msg, gen_cmd in gen_results:
        test_gen_cmd_map[stem] = gen_cmd
        if test_file:
            test_map[stem] = test_file
            if sequential:
                print(f"[run_evaluation]   OK: {test_file.name}")
        else:
            logger.warning("Test generation failed for %s: %s", f"{stem}.dfy", error_msg)
            if sequential:
                print(f"[run_evaluation]   FAILED: {error_msg}")

    if not test_map:
        logger.error("Test generation failed for all programs — aborting.")
        return 1

    if sequential:
        print(f"[run_evaluation] Tests generated for {len(test_map)}/{len(originals)} programs")

    # --- Step 2: Kill check each mutant ---
    mutants = sorted(killed_dir.glob("*.dfy"))
    if not mutants:
        logger.error("No .dfy mutant files found in killed/")
        return 1

    # Build kill check tasks: (test_file, mutant_file) pairs
    kill_tasks: list[tuple[Path, Path]] = []
    skipped_mutants = 0
    for mutant in mutants:
        orig_stem = _derive_original_stem(mutant.name)
        if orig_stem in test_map:
            kill_tasks.append((test_map[orig_stem], mutant))
        else:
            skipped_mutants += 1
            if sequential:
                print(f"[run_evaluation] Skipping mutant {mutant.name} — no test for {orig_stem}")

    if not kill_tasks:
        logger.error("No mutants matched to generated tests — aborting.")
        return 1

    if sequential:
        print(f"[run_evaluation] Running kill checks on {len(kill_tasks)} mutants...")

    checker = KillChecker()

    def _check_kill_task(task: tuple[Path, Path]) -> MutantResult:
        test_file, mutant_file = task
        return checker.check_kill(test_file, mutant_file)

    parallel = not sequential
    results: list[MutantResult] = run_parallel_or_seq(
        kill_tasks,
        _check_kill_task,
        "Kill checking",
        parallel=parallel,
    )

    if sequential:
        for r in results:
            print(
                f"[run_evaluation]   {r.mutant_name}: {r.status.value} "
                f"({r.execution_time:.1f}s)"
            )

    # Attach test generation command to each result
    for r in results:
        orig_stem = _derive_original_stem(r.mutant_name)
        r.test_gen_command = test_gen_cmd_map.get(orig_stem, "")

    # --- Step 3: Compute metrics ---
    metrics = compute_kill_rate(results)

    # --- Step 4: Report ---
    print_summary(metrics)

    output_dir.mkdir(parents=True, exist_ok=True)
    results_file = output_dir / "results.json"
    write_json_results(
        results,
        metrics,
        results_file,
        dataset_name=dataset_path.name,
        generator_name=generator.name,
    )

    if sequential:
        print(f"[run_evaluation] Results written to {results_file}")

    return 0


def main(argv: list[str] | None = None) -> None:
    """Entry point."""
    args = parse_args(argv)

    dataset_path = Path(args.dataset_path)
    output_dir = Path(args.output_dir) if args.output_dir else dataset_path

    exit_code = run_pipeline(
        dataset_path,
        clean_cache=args.clean_cache,
        sequential=args.sequential,
        output_dir=output_dir,
    )
    sys.exit(exit_code)


if __name__ == "__main__":
    main()
