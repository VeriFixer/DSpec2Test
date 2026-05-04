"""Summary reporter: stdout table and JSON results file."""

import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

from src.mt_eval.core.models import MutantResult
from src.mt_eval.metrics.kill_rate import KillRateMetrics


def print_summary(metrics: KillRateMetrics) -> None:
    """Print a summary table to stdout.

    Columns: total, killed, survived, timeout, kill_rate.
    """
    header = f"{'Total':>8} {'Killed':>8} {'Survived':>10} {'Timeout':>9} {'Kill Rate':>10}"
    row = (
        f"{metrics.total:>8} {metrics.killed:>8} {metrics.survived:>10} "
        f"{metrics.timeout:>9} {metrics.kill_rate:>9.1%}"
    )
    sep = "-" * len(header)
    print(sep)
    print(header)
    print(sep)
    print(row)
    print(sep)


def write_json_results(
    results: list[MutantResult],
    metrics: KillRateMetrics,
    output_path: Path,
    *,
    dataset_name: str = "unknown",
    generator_name: str = "unknown",
) -> None:
    """Write JSON results file with metadata, summary, and per-mutant entries.

    Args:
        results: Per-mutant result list.
        metrics: Aggregated kill rate metrics.
        output_path: Destination file path.
        dataset_name: Name of the dataset (for metadata).
        generator_name: Name of the test generator (for metadata).
    """
    payload: dict[str, Any] = {
        "metadata": {
            "dataset": dataset_name,
            "generator": generator_name,
            "timestamp": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "total_mutants": metrics.total,
        },
        "summary": {
            "killed": metrics.killed,
            "survived": metrics.survived,
            "timeout": metrics.timeout,
            "kill_rate": metrics.kill_rate,
        },
        "results": [r.to_dict() for r in results],
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
