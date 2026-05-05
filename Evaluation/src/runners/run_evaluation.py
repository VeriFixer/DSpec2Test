"""Evaluation runner — generate tests, safety check, kill check, report.

CLI entry point for running mutation kill evaluation on selected programs.

Usage:
    python -m src.runners.run_evaluation [--sequential] [--output-dir DIR]
"""

import argparse
import json
import logging
import sys
from pathlib import Path

from src.config import (
    SELECTED_PROGRAMS_DIR,
    SELECTED_PROGRAMS_MUTANTS_DIR,
    SELECTED_PROGRAMS_MUTANTS_WITH_TESTS_DIR,
)
from src.mt_eval.core.models import MutantResult, MutantStatus
from src.mt_eval.execution.kill_checker import KillChecker
from src.mt_eval.execution.parallel_executor import run_parallel_or_seq
from src.mt_eval.execution.safety_check import run_safety_check
from src.mt_eval.generators.spec_test_generator import SpecTestGenerator
from src.mt_eval.metrics.pipeline_stats import PipelineStats

logger = logging.getLogger(__name__)


def _map_mutants(mutants_dir: Path) -> dict[str, list[Path]]:
    """Map original_stem → list of mutant paths.

    Naming convention: <original_stem>__<rest>.dfy
    """
    mapping: dict[str, list[Path]] = {}
    for mutant in sorted(mutants_dir.glob("**/*.dfy")):
        stem = mutant.stem
        if "__" in stem:
            original_stem = stem.split("__")[0]
        else:
            original_stem = stem
        mapping.setdefault(original_stem, []).append(mutant)
    return mapping


def run_pipeline(sequential: bool = False, output_dir: Path | None = None,
                 verbose: bool = False, max_display: int | None = None) -> int:
    """Execute the evaluation pipeline.

    Returns 0 on success, 1 on critical failure.
    """
    if output_dir is None:
        output_dir = Path("results")

    # --- Step 1: Read originals ---
    originals = sorted(SELECTED_PROGRAMS_DIR.glob("*.dfy"))
    if not originals:
        logger.error("No .dfy files found in %s", SELECTED_PROGRAMS_DIR)
        return 1

    # --- Step 2: Read mutants ---
    mutant_map = _map_mutants(SELECTED_PROGRAMS_MUTANTS_DIR)
    if not mutant_map:
        logger.error("No .dfy mutant files found in %s", SELECTED_PROGRAMS_MUTANTS_DIR)
        return 1

    print(f"[run_evaluation] {len(originals)} originals, "
          f"{sum(len(v) for v in mutant_map.values())} mutants")

    # --- Step 3: For each strategy ---
    strategies = [SpecTestGenerator()]

    for strategy in strategies:
        print(f"\n[run_evaluation] Strategy: {strategy.name}")

        # Track stats
        not_supported_programs = 0
        not_supported_mutants = 0
        total_mutants = sum(len(mutant_map.get(o.stem, [])) for o in originals)
        results: list[MutantResult] = []

        # 3a. Generate tests for each original
        tests_dir = SELECTED_PROGRAMS_DIR.parent / "tests"
        tests_dir.mkdir(parents=True, exist_ok=True)

        def _gen_test(orig: Path) -> tuple[str, Path | None, str]:
            test_file = tests_dir / f"{orig.stem}.test.dfy"
            result = strategy.generate_tests(orig, test_file)
            if result.success and result.test_file:
                return (orig.stem, result.test_file, result.command)
            logger.warning("Test generation failed for %s: %s", orig.name, result.error_message)
            return (orig.stem, None, result.command)

        parallel = not sequential
        gen_results: list[tuple[str, Path | None, str]] = run_parallel_or_seq(
            originals, _gen_test, "Test generation", parallel=parallel,
        )

        test_map: dict[str, Path] = {}
        test_gen_cmd_map: dict[str, str] = {}
        for stem, test_file, cmd in gen_results:
            test_gen_cmd_map[stem] = cmd
            if test_file:
                test_map[stem] = test_file

        # 3b. Safety check + kill check per original
        supported_originals: list[Path] = []
        not_supported_details: list[dict] = []
        for orig in originals:
            if orig.stem not in test_map:
                # No tests generated — mark not supported
                n_mutants = len(mutant_map.get(orig.stem, []))
                not_supported_programs += 1
                not_supported_mutants += n_mutants
                not_supported_details.append({
                    "program": orig.name,
                    "reason": "test_generation_failed",
                    "mutants_skipped": n_mutants,
                })
                continue

            test_file = test_map[orig.stem]
            safe = run_safety_check(orig, test_file)

            if not safe:
                n_mutants = len(mutant_map.get(orig.stem, []))
                not_supported_programs += 1
                not_supported_mutants += n_mutants
                not_supported_details.append({
                    "program": orig.name,
                    "reason": "safety_check_failed",
                    "mutants_skipped": n_mutants,
                })
                if sequential:
                    print(f"  [NOT SUPPORTED] {orig.name} — safety check failed")
                continue

            supported_originals.append(orig)

        # 3c. Kill check supported mutants
        kill_tasks: list[tuple[Path, Path]] = []
        for orig in supported_originals:
            test_file = test_map[orig.stem]
            for mutant in mutant_map.get(orig.stem, []):
                kill_tasks.append((test_file, mutant))

        if kill_tasks:
            checker = KillChecker(
                output_dir=SELECTED_PROGRAMS_MUTANTS_WITH_TESTS_DIR,
                originals_dir=SELECTED_PROGRAMS_DIR,
            )

            def _check_kill(task: tuple[Path, Path]) -> MutantResult:
                test_file, mutant_file = task
                return checker.check_kill(test_file, mutant_file)

            kill_results: list[MutantResult] = run_parallel_or_seq(
                kill_tasks, _check_kill, "Kill checking", parallel=parallel,
            )
            # Attach test generation command to each result
            for r in kill_results:
                orig_stem = r.original_name.removesuffix(".dfy")
                r.test_gen_command = test_gen_cmd_map.get(orig_stem, "")
            results.extend(kill_results)

        # 3d. Compute stats
        killed = sum(1 for r in results if r.status == MutantStatus.KILLED)
        survived = sum(1 for r in results if r.status == MutantStatus.SURVIVED)
        timeout = sum(1 for r in results if r.status == MutantStatus.TIMEOUT)
        error = sum(1 for r in results if r.status == MutantStatus.ERROR)

        stats = PipelineStats(
            total_programs=len(originals),
            not_supported_programs=not_supported_programs,
            total_mutants=total_mutants,
            not_supported_mutants=not_supported_mutants,
            killed=killed,
            survived=survived,
            timeout=timeout,
            error=error,
        )

        # 3g. Verbose per-mutant output
        if verbose and results:
            display_results = results[:max_display] if max_display else results
            print(f"\n{'─'*60}")
            print(f"  VERBOSE: Per-mutant details ({len(display_results)}"
                  f"{'/' + str(len(results)) if max_display else ''} shown)")
            print(f"{'─'*60}")
            for r in display_results:
                status_icon = {
                    MutantStatus.KILLED: "✗ KILLED",
                    MutantStatus.SURVIVED: "✓ SURVIVED",
                    MutantStatus.TIMEOUT: "⏱ TIMEOUT",
                    MutantStatus.ERROR: "⚠ ERROR",
                }[r.status]
                print(f"\n  [{status_icon}] {r.mutant_name} ({r.execution_time:.1f}s)")
                print(f"    Original: {r.original_name}")
                if r.test_gen_command:
                    print(f"    Test gen: {r.test_gen_command}")
                print(f"    Kill cmd: {r.kill_check_command}")
                if r.stdout:
                    stdout_lines = r.stdout.splitlines()[:5]
                    print(f"    stdout: {stdout_lines[0]}")
                    for line in stdout_lines[1:]:
                        print(f"            {line}")
                if r.stderr:
                    stderr_lines = r.stderr.splitlines()[:5]
                    print(f"    stderr: {stderr_lines[0]}")
                    for line in stderr_lines[1:]:
                        print(f"            {line}")
            print(f"\n{'─'*60}")
            
        # 3e. Print summary
        print(f"\n{'='*60}")
        print(f"  Strategy: {strategy.name}")
        print(f"{'='*60}")
        print(f"  Programs: {stats.total_programs} total")
        print(f"    Supported:     {stats.total_programs - stats.not_supported_programs}")
        print(f"    Not-supported: {stats.not_supported_programs} "
              f"({stats.not_supported_program_rate:.1%})")
        for detail in not_supported_details:
            print(f"      - {detail['program']}: {detail['reason']} "
                  f"({detail['mutants_skipped']} mutants skipped)")
        print(f"  Mutants: {stats.total_mutants} total")
        print(f"    Supported:     {stats.supported_mutants}")
        print(f"    Not-supported: {stats.not_supported_mutants} "
              f"({stats.not_supported_mutant_rate:.1%})")
        print(f"  Kill results (supported only):")
        print(f"    Killed:   {stats.killed}")
        print(f"    Survived: {stats.survived}")
        print(f"    Timeout:  {stats.timeout}")
        print(f"    Error:    {stats.error}")
        print(f"  Kill rate: {stats.kill_rate:.2%}")
        print(f"{'='*60}\n")

        # 3f. Write JSON
        output_dir.mkdir(parents=True, exist_ok=True)
        results_file = output_dir / "results.json"
        output_data = {
            "strategy": strategy.name,
            "stats": stats.to_dict(),
            "not_supported": not_supported_details,
            "results": [r.to_dict() for r in results],
        }
        results_file.write_text(json.dumps(output_data, indent=2) + "\n")
        print(f"[run_evaluation] Results written to {results_file}")



    return 0


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse CLI arguments."""
    parser = argparse.ArgumentParser(
        description="Run mutation kill evaluation on selected programs."
    )
    parser.add_argument(
        "--sequential",
        action="store_true",
        default=False,
        help="Disable parallel execution",
    )
    parser.add_argument(
        "--output-dir",
        type=str,
        default=None,
        help="Directory for results JSON (default: results/)",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        default=False,
        help="Print per-mutant details (test gen cmd, kill output) after summary",
    )
    parser.add_argument(
        "--max-display",
        type=int,
        default=None,
        help="Max number of mutant results to display in verbose mode (default: all)",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> None:
    """Entry point."""
    args = parse_args(argv)
    out = Path(args.output_dir) if args.output_dir else None
    exit_code = run_pipeline(
        sequential=args.sequential,
        output_dir=out,
        verbose=args.verbose,
        max_display=args.max_display,
    )
    sys.exit(exit_code)


if __name__ == "__main__":
    main()
