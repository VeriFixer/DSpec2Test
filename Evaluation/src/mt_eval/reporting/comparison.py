"""Comparison reporting for multi-strategy evaluation."""

import json
from pathlib import Path


def print_comparison_table(all_stats: dict[str, dict]) -> None:
    """Print side-by-side comparison table to stdout.

    Skips if only one strategy.

    all_stats: mapping of strategy_name -> output_data dict with keys:
        "strategy", "stats", "not_supported", "results"
    The "stats" sub-dict has: kill_rate, killed, survived,
        not_supported_programs, not_supported_mutants, etc.
    """
    if len(all_stats) <= 1:
        return

    headers = ["Strategy", "Kill Rate", "Killed", "Survived", "Not-Supported Programs", "Not-Supported Mutants"]

    rows: list[list[str]] = []
    for name, data in all_stats.items():
        stats = data["stats"]
        rows.append([
            name,
            f"{stats['kill_rate'] * 100:.2f}%",
            str(stats["killed"]),
            str(stats["survived"]),
            str(stats["not_supported_programs"]),
            str(stats["not_supported_mutants"]),
        ])

    # Compute column widths
    col_widths = [len(h) for h in headers]
    for row in rows:
        for i, cell in enumerate(row):
            col_widths[i] = max(col_widths[i], len(cell))

    def format_row(cells: list[str]) -> str:
        return " | ".join(cell.ljust(col_widths[i]) for i, cell in enumerate(cells))

    separator = "-+-".join("-" * w for w in col_widths)

    print(format_row(headers))
    print(separator)
    for row in rows:
        print(format_row(row))


def write_comparison_json(all_stats: dict[str, dict], output_path: Path) -> None:
    """Write comparison.json with all strategy stats and best_kill_rate.

    Output format:
    {
        "strategies": { "name": { stats dict }, ... },
        "best_kill_rate": "name_with_highest_kill_rate"
    }
    """
    strategies_stats: dict[str, dict] = {}
    best_name = ""
    best_rate = -1.0

    for name, data in all_stats.items():
        stats = data["stats"]
        strategies_stats[name] = stats
        if stats["kill_rate"] > best_rate:
            best_rate = stats["kill_rate"]
            best_name = name

    output = {
        "strategies": strategies_stats,
        "best_kill_rate": best_name,
    }

    output_path.parent.mkdir(parents=True, exist_ok=True)
    output_path.write_text(json.dumps(output, indent=2) + "\n")
