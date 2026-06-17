"""Evaluation runner — generate tests, safety check, kill check, report.

CLI entry point for running mutation kill evaluation on selected programs.

Usage:
    python -m src.runners.run_evaluation [--sequential] [--output-dir DIR]
"""

import argparse
import json
import shutil
import sys
import re
import statistics
import time
import datetime
from pathlib import Path

from src.logging_config import get_logger
from src.config import (
    SELECTED_PROGRAMS_DIR,
    SELECTED_PROGRAMS_MUTANTS_DIR,
)
from src.mt_eval.core.models import MutantResult, MutantStatus
from src.mt_eval.execution.kill_checker import KillChecker
from src.mt_eval.execution.parallel_executor import run_parallel_or_seq, shutdown_parallel_executor
from src.mt_eval.execution.safety_check import run_safety_check, SafetyCheckResult
from src.mt_eval.generators import STRATEGY_REGISTRY, resolve_strategies
from src.mt_eval.metrics.pipeline_stats import PipelineStats
from src.mt_eval.reporting.comparison import print_comparison_table, write_comparison_json
from src.mt_eval.paths import (
    get_strategy_combined_dir, 
    get_strategy_tests_dir,
    get_strategy_results_path,
    get_strategy_tmp_exec_dir,
    get_strategy_debug_dir,
    get_strategy_all_dir
)

logger = get_logger(__name__)

def _get_test_count(dfy_file: Path) -> int:
    """Parses a Dafny file and returns the total number of test methods."""
    if not dfy_file.exists():
        return 0
    content = dfy_file.read_text(encoding='utf-8')
    pattern = re.compile(r'method\s+\{\s*:test\}\s+([a-zA-Z0-9_]+)')
    return len(set(pattern.findall(content)))

def _split_tests(test_file: Path, total_reps: int, base_tests_dir: Path, fallback_time: float) -> dict[int, tuple[Path, float, bool]]:
    """Parses the generated test file, splits by // REPEAT comments, and creates isolated files per rep."""
    if not test_file.exists():
        return {}
    
    lines = test_file.read_text(encoding='utf-8').splitlines()
    reps_content = {i: [] for i in range(1, total_reps + 1)}
    avg_fallback = fallback_time / total_reps if total_reps > 0 else fallback_time
    reps_time = {i: avg_fallback for i in range(1, total_reps + 1)}
    current_rep = 1
    
    rep_pattern = re.compile(r'//\s*REPEAT\s+(\d+)\s*-\s*TIME:\s*([0-9.]+)\s*s?')
    
    for line in lines:
        if current_rep <= total_reps:
            reps_content[current_rep].append(line)
        
        match = rep_pattern.search(line)
        if match:
            parsed_rep = int(match.group(1))
            parsed_time = float(match.group(2))
            reps_time[current_rep] = parsed_time
            current_rep = min(parsed_rep + 1, total_reps)
            
    last_valid_content = []
    last_valid_time = avg_fallback
    
    accumulated_paths = {}
    
    for r in range(1, total_reps + 1):
        is_forward_filled = False
        if any(line.strip() for line in reps_content[r]):
            last_valid_content = reps_content[r]
            last_valid_time = reps_time[r]
        else:
            reps_content[r] = last_valid_content.copy()
            reps_time[r] = last_valid_time
            is_forward_filled = True
            
        rep_time = reps_time[r]
        
        rep_dir = base_tests_dir / f"rep_{r}"
        rep_dir.mkdir(parents=True, exist_ok=True)
        
        out_path = rep_dir / test_file.name
        out_path.write_text("\n".join(reps_content[r]), encoding='utf-8')
        
        accumulated_paths[r] = (out_path, rep_time, is_forward_filled)
        
    return accumulated_paths

def _map_mutants(mutants_dir: Path) -> dict[str, list[Path]]:
    """Map original_stem → list of mutant paths.

    Naming convention: <original_stem>__<rest>.dfy
    """
    mapping: dict[str, list[Path]] = {}
    for mutant in sorted(mutants_dir.glob("**/*.dfy")):
        stem = mutant.stem
        if "__" in stem:
            original_stem = stem.rsplit("__", 1)[0]
        else:
            original_stem = stem
        mapping.setdefault(original_stem, []).append(mutant)
    return mapping


def run_pipeline(sequential: bool = False, output_dir: Path | None = None,
                 verbose: bool = False, max_display: int | None = None,
                 strategies=None, clean_cache: bool = False, repeat: int = 1) -> int:
    """Execute the evaluation pipeline.

    Returns 0 on success, 1 on critical failure.
    """
    if output_dir is None:
        output_dir = Path("results")

    if strategies is None:
        strategies = resolve_strategies(list(STRATEGY_REGISTRY.keys()))

    if clean_cache:
        from src.config import BASE_PATH as _base
        for strategy in strategies:
            mode = strategy.mode
            # Delete per-strategy combined dir
            combined = _base / "dataset_output" / f"selected_programs_mutants_with_tests_{mode}"
            if combined.exists():
                shutil.rmtree(combined)
            # Delete per-strategy tests dir
            tests = _base / "dataset_output" / f"tests_{mode}"
            if tests.exists():
                shutil.rmtree(tests)
            # Delete per-strategy results dir
            strategy_results_dir = output_dir / f"results_{mode}"
            if strategy_results_dir.exists():
                shutil.rmtree(strategy_results_dir)
        # Delete comparison.json
        comparison_path = output_dir / "comparison.json"
        if comparison_path.exists():
            comparison_path.unlink()

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
    all_strategy_results: dict[str, dict] = {}

    for strategy in strategies:
        print(f"\n[run_evaluation] Strategy: {strategy.mode}")

        strategy_output_dir = output_dir / f"results_{strategy.mode}"

        expected_last_rep_file = strategy_output_dir / f"results_{strategy.mode}_rep_{repeat}.json"
        
        if expected_last_rep_file.exists():
            print(f"[run_evaluation] Cache hit for {strategy.mode}, loading from {strategy_output_dir}")
            for rep in range(1, repeat + 1):
                rep_file = strategy_output_dir / f"results_{strategy.mode}_rep_{rep}.json"
                if rep_file.exists():
                    rep_strategy_key = f"{strategy.mode}_rep_{rep}"
                    all_strategy_results[rep_strategy_key] = json.loads(rep_file.read_text())
            continue

        # 3a. Generate tests for each original
        tests_dir = get_strategy_tests_dir(strategy.mode)
        strategy_combined_dir = get_strategy_combined_dir(strategy.mode)
        tmp_exec_dir = get_strategy_tmp_exec_dir(strategy_combined_dir)
        debug_dir = get_strategy_debug_dir(strategy_combined_dir)

        def _gen_test(orig: Path) -> tuple[str, Path | None, str, float]:
            test_file = tests_dir / f"{orig.stem}.test.dfy"
            result = strategy.generate_tests(orig, test_file, repeat)
            if result.success and result.test_file:
                return (orig.stem, result.test_file, result.command, result.execution_time)
            logger.warning("Test generation failed for %s: %s\n  Command: %s",
                         orig.name, result.error_message, result.command)
            return (orig.stem, None, result.command, result.execution_time)

        parallel = not sequential
        gen_results: list[tuple[str, Path | None, str, float]] = run_parallel_or_seq(
            originals, _gen_test, "Test generation", parallel=parallel,
        )

        test_map: dict[str, Path] = {}
        test_gen_cmd_map: dict[str, str] = {}
        test_gen_time_map: dict[str, float] = {}
        for stem, test_file, cmd, gen_time in gen_results:
            test_gen_cmd_map[stem] = cmd
            test_gen_time_map[stem] = gen_time
            if test_file:
                test_map[stem] = test_file

        # 3b. Split tests (isolate reps into combined dir)
        split_data: dict[str, dict[int, tuple[Path, float, bool]]] = {}
        originals_with_tests = [o for o in originals if o.stem in test_map]
        originals_without_tests = [o for o in originals if o.stem not in test_map]

        for orig in originals_with_tests:
            total_time = test_gen_time_map.get(orig.stem, 0.0)
            split_data[orig.stem] = _split_tests(test_map[orig.stem], repeat, tmp_exec_dir, total_time)

        # Initialize tracking variables across reps
        supported_originals = originals_with_tests.copy()
        not_supported_details = []
        not_supported_programs = 0
        not_supported_mutants = 0
        total_mutants = sum(len(mutant_map.get(o.stem, [])) for o in originals)

        # Mark programs with no tests as not supported initially
        for orig in originals_without_tests:
            n_mutants = len(mutant_map.get(orig.stem, []))
            not_supported_programs += 1
            not_supported_mutants += n_mutants
            not_supported_details.append({
                "program": orig.name,
                "reason": "test_generation_failed",
                "failed_step": "test_generation",
                "mutants_skipped": n_mutants,
                "test_gen_command": test_gen_cmd_map.get(orig.stem, ""),
                "test_gen_time": test_gen_time_map.get(orig.stem, 0.0),
            })

        cumulative_safety_time = {orig.stem: 0.0 for orig in originals}
        cumulative_test_counts = {orig.stem: 0 for orig in originals}
        
        mutant_status_tracker: dict[str, MutantResult] = {}
        mutant_accumulated_time: dict[str, float] = {}

        for rep in range(1, repeat + 1):
            print(f"\n[run_evaluation] --- Running Repetition {rep}/{repeat} ---")

            rep_test_gen_time = {
                orig.stem: split_data.get(orig.stem, {}).get(rep, (None, 0.0))[1]
                for orig in originals
            }

            rep_debug_dir = debug_dir / f"rep_{rep}"
            rep_debug_dir.mkdir(parents=True, exist_ok=True)
            

            # 3c. Safety check per original using isolated rep tests
            safety_tasks = [
                orig for orig in supported_originals
                if not split_data[orig.stem][rep][2] 
            ]

            def _safety_check(orig: Path) -> tuple[Path, SafetyCheckResult]:
                rep_test_file = split_data[orig.stem][rep][0]
                result = run_safety_check(orig, rep_test_file, artifacts_dir=rep_debug_dir)
                return (orig, result)

            safety_results: list[tuple[Path, SafetyCheckResult]] = run_parallel_or_seq(
                safety_tasks, _safety_check, f"Safety check (Rep {rep})", parallel=parallel,
            )

            newly_failed_originals = []
            for orig, safety_result in safety_results:
                cumulative_safety_time[orig.stem] += safety_result.execution_time

                if not safety_result.passed:
                    n_mutants = len(mutant_map.get(orig.stem, []))
                    not_supported_programs += 1
                    not_supported_mutants += n_mutants
                    detail: dict = {
                        "program": orig.name,
                        "reason": f"safety_check_failed_rep_{rep}",
                        "failed_step": "safety_check",
                        "mutants_skipped": n_mutants,
                        "test_gen_command": test_gen_cmd_map.get(orig.stem, ""),
                        "test_gen_time": split_data.get(orig.stem, {}).get(rep, (None, test_gen_time_map.get(orig.stem, 0.0)))[1],
                        "safety_check_command": safety_result.command,
                        "safety_check_time": safety_result.execution_time,
                        "safety_file": safety_result.safety_file,
                    }
                    if safety_result.error_message:
                        detail["error_message"] = safety_result.error_message
                    if safety_result.stdout:
                        detail["stdout"] = safety_result.stdout
                    if safety_result.stderr:
                        detail["stderr"] = safety_result.stderr
                    not_supported_details.append(detail)
                    newly_failed_originals.append(orig)
                    if sequential:
                        print(f"  [NOT SUPPORTED] {orig.name} — safety check failed in rep {rep}")
                    continue

            for orig in newly_failed_originals:
                supported_originals.remove(orig)

            # Accumulate test stats strictly for supported originals
            for orig in supported_originals:
                rep_test_file = split_data[orig.stem][rep][0]
                cumulative_test_counts[orig.stem] += _get_test_count(rep_test_file)

            # 3d. Kill check supported mutants
            kill_tasks: list[tuple[Path, Path]] = []
            for orig in supported_originals:
                rep_test_file, _, is_forward_filled = split_data[orig.stem][rep]

                if is_forward_filled:
                    continue

                for mutant in mutant_map.get(orig.stem, []):
                    m_name = mutant.name
                    prev_res = mutant_status_tracker.get(m_name)
                    # Skip redundant work if it was already killed or timed-out in a previous rep
                    if prev_res and (prev_res.status == MutantStatus.KILLED or prev_res.status == MutantStatus.TIMEOUT):
                        continue
                    kill_tasks.append((rep_test_file, mutant))

            if kill_tasks:
                checker = KillChecker(
                    output_dir=rep_debug_dir,
                    originals_dir=SELECTED_PROGRAMS_DIR,
                )

                def _check_kill(task: tuple[Path, Path]) -> MutantResult:
                    test_file, mutant_file = task
                    return checker.check_kill(test_file, mutant_file)

                kill_results: list[MutantResult] = run_parallel_or_seq(
                    kill_tasks, _check_kill, f"Kill checking (Rep {rep})", parallel=parallel,
                )
                
                for r in kill_results:
                    m_name = r.mutant_name
                    
                    # Accumulate execution time
                    prev_time = mutant_accumulated_time.get(m_name, 0.0)
                    new_time = prev_time + r.execution_time
                    mutant_accumulated_time[m_name] = new_time
                    r.execution_time = new_time
                    
                    orig_stem = r.original_name.removesuffix(".dfy")
                    r.test_gen_command = test_gen_cmd_map.get(orig_stem, "")
                    r.test_gen_time = rep_test_gen_time.get(orig_stem, 0.0)
                    r.safety_check_time = cumulative_safety_time.get(orig_stem, 0.0)
                    
                    mutant_status_tracker[m_name] = r

            # Reconstruct complete rep_results to accurately compute stats
            rep_results: list[MutantResult] = []
            for orig in supported_originals:
                for mutant in mutant_map.get(orig.stem, []):
                    if mutant.name in mutant_status_tracker:
                        res = mutant_status_tracker[mutant.name]
                        
                        res.test_gen_time = rep_test_gen_time.get(orig.stem, 0.0)
                        res.safety_check_time = cumulative_safety_time.get(orig.stem, 0.0)
                        
                        rep_results.append(res)

            # 3e. Compute stats
            killed = sum(1 for r in rep_results if r.status == MutantStatus.KILLED)
            survived = sum(1 for r in rep_results if r.status == MutantStatus.SURVIVED)
            timeout = sum(1 for r in rep_results if r.status == MutantStatus.TIMEOUT)
            error = sum(1 for r in rep_results if r.status == MutantStatus.ERROR)

            test_counts = [cumulative_test_counts[orig.stem] for orig in supported_originals]
            total_num_tests = sum(test_counts) if test_counts else 0
            avg_num_tests = (total_num_tests / len(test_counts)) if test_counts else 0.0
            median_num_tests = statistics.median(test_counts) if test_counts else 0

            stats = PipelineStats(
                total_programs=len(originals),
                not_supported_programs=not_supported_programs,
                total_mutants=total_mutants,
                not_supported_mutants=not_supported_mutants,
                killed=killed,
                survived=survived,
                timeout=timeout,
                error=error,
                total_num_tests=total_num_tests,
                avg_num_tests=avg_num_tests,
                median_num_tests=median_num_tests
            )

            # 3f. Verbose per-mutant output
            if verbose and rep_results:
                display_results = rep_results[:max_display] if max_display else rep_results
                print(f"\n{'─'*60}")
                print(f"  VERBOSE: Per-mutant details ({len(display_results)}"
                    f"{'/' + str(len(rep_results)) if max_display else ''} shown)")
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
                        print(f"    Test gen: {r.test_gen_command} ({r.test_gen_time:.1f}s)")
                    if r.safety_check_time:
                        print(f"    Safety check: {r.safety_check_time:.1f}s")
                    print(f"    Kill cmd: {r.kill_check_command} ({r.execution_time:.1f}s)")
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

            # 3g. Print summary
            print(f"\n{'='*60}")
            print(f"  Strategy: {strategy.mode} | Repetition: {rep}")
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
            print(f"  Tests Generated:")
            print(f"    Total:    {total_num_tests}")
            print(f"    Average:  {avg_num_tests:.2f} per file")
            print(f"    Median:   {median_num_tests} per file")
            print(f"  Kill results (supported only):")
            print(f"    Killed:   {stats.killed}")
            print(f"    Survived: {stats.survived}")
            print(f"    Timeout:  {stats.timeout}")
            print(f"    Error:    {stats.error}")
            print(f"  Kill rate: {stats.kill_rate:.2%}")
            print(f"  Not surived rate: {stats.not_survived_rate:.2%}")
            print(f"{'='*60}\n")

            # 3h-timing. Per-program timing summary
            """ print(f"  {'─'*56}")
            print(f"  TIMING SUMMARY (per program):")
            print(f"  {'─'*56}")
            print(f"  {'Program':<30} {'TestGen':>8} {'Safety':>8} {'Kill(avg)':>10}")
            print(f"  {'─'*56}")
            for orig in originals:
                tg = rep_test_gen_time.get(orig.stem, 0.0)
                sc = cumulative_safety_time.get(orig.stem, 0.0)
                tc = cumulative_test_counts.get(orig.stem, 0)
                # Average kill time for this program's mutants
                prog_kills = [r for r in rep_results if r.original_name == f"{orig.stem}.dfy"]
                avg_kill = (sum(r.execution_time for r in prog_kills) / len(prog_kills)
                            if prog_kills else 0.0)
                print(f"  {orig.stem:<30} {tg:>7.1f}s {sc:>7.1f}s {avg_kill:>9.1f}s {tc:>5}")
            print(f"  {'─'*56}\n") """

            # 3i. Write JSON
            output_dir.mkdir(parents=True, exist_ok=True)
            strategy_output_dir = output_dir / f"results_{strategy.mode}"
            strategy_output_dir.mkdir(parents=True, exist_ok=True)

            rep_strategy_key = f"{strategy.mode}_rep_{rep}"
            results_file = get_strategy_results_path(rep_strategy_key, strategy_output_dir)
            output_data = {
                "strategy": strategy.mode,
                "repetition": rep,
                "stats": stats.to_dict(),
                "timing": {
                    "per_program": {
                        orig.stem: {
                            "test_gen_time": rep_test_gen_time.get(orig.stem, 0.0),
                            "safety_check_time": cumulative_safety_time.get(orig.stem, 0.0),
                        }
                        for orig in originals
                    },
                },
                "test_counts": {
                    "per_program": {
                        orig.stem: cumulative_test_counts.get(orig.stem, 0)
                        for orig in originals
                    }
                },
                "not_supported": not_supported_details,
                "results": [r.to_dict() for r in rep_results],
            }
            results_file.write_text(json.dumps(output_data, indent=2) + "\n")
            print(f"[run_evaluation] Results written to {results_file}")
            all_strategy_results[rep_strategy_key] = output_data

        
        # --- Step 3.j: Generate the "all" folder for clean artifacts ---
        print(f"\n[run_evaluation] Generating all supported combined files for {strategy.mode}...")
        all_dir = get_strategy_all_dir(strategy_combined_dir)

        for orig in originals:
            full_test_file = test_map.get(orig.stem)
            if not full_test_file or not full_test_file.exists():
                continue
            
            full_test_content = full_test_file.read_text(encoding='utf-8')
            
            for mutant in mutant_map.get(orig.stem, []):
                if mutant.name not in mutant_status_tracker:
                    continue
                
                mutant_content = mutant.read_text(encoding='utf-8')
                combined_content = f"{mutant_content}\n\n{full_test_content}"
                
                out_path = all_dir / f"{mutant.stem}.test.dfy"
                out_path.write_text(combined_content, encoding='utf-8')

        # --- Step 3.k: Clean up temporary files ---
        print(f"[run_evaluation] Cleaning up temporary execution files for {strategy.mode}...")
        if tmp_exec_dir.exists():
            shutil.rmtree(tmp_exec_dir)

    # --- Step 4: Comparison summary ---
    print_comparison_table(all_strategy_results)
    comparison_path = output_dir / "comparison.json"
    write_comparison_json(all_strategy_results, comparison_path)
    print(f"[run_evaluation] Comparison written to {comparison_path}")

    # --- Cleanup: shut down thread pool so process can exit ---
    shutdown_parallel_executor(wait=False)

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
    parser.add_argument(
        "--strategies",
        type=str,
        default="all",
        help="Comma-separated strategy mode names to run, or 'all' (default: all)",
    )
    parser.add_argument(
        "--clean-cache",
        action="store_true",
        default=False,
        help="Delete cached per-strategy results and combined dirs before running",
    )
    parser.add_argument(
        "--repeat",
        type=int,
        default=1,
        help="Repeat flag for generate-tests command",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> None:
    """Entry point."""
    logger.info(f"Started at: {datetime.datetime.now()}")
    start_time = time.time()

    args = parse_args(argv)
    out = Path(args.output_dir) if args.output_dir else None

    # Resolve strategies
    if args.strategies == "all":
        strategy_names = list(STRATEGY_REGISTRY.keys())
    else:
        strategy_names = [s.strip() for s in args.strategies.split(",")]

    try:
        resolved = resolve_strategies(strategy_names)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

    exit_code = run_pipeline(
        sequential=args.sequential,
        output_dir=out,
        verbose=args.verbose,
        max_display=args.max_display,
        strategies=resolved,
        clean_cache=args.clean_cache,
        repeat=args.repeat
    )

    end_time = time.time()
    elapsed_time = end_time - start_time
    logger.info(f"Total run_evaluation.py time: {elapsed_time / 3600:.4f} hours")
    logger.info(f"Finished at: {datetime.datetime.now()}")
    sys.exit(exit_code)


if __name__ == "__main__":
    main()