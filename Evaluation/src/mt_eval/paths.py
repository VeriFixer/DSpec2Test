"""Per-strategy path derivation utilities.

Derives output directories and results file paths from strategy mode/name.
"""

from pathlib import Path

from src.config import BASE_PATH


def get_strategy_combined_dir(mode: str, base_path: Path | None = None) -> Path:
    """Return per-strategy combined test+mutant directory, creating it if needed.

    Path: base_path / dataset / selected_programs_mutants_with_tests_{mode}/
    """
    root = base_path if base_path is not None else BASE_PATH
    combined_dir = root / "dataset" / f"selected_programs_mutants_with_tests_{mode}"
    combined_dir.mkdir(parents=True, exist_ok=True)
    return combined_dir


def get_strategy_results_path(strategy_name: str, output_dir: Path) -> Path:
    """Return per-strategy results JSON path.

    Path: output_dir / results_{strategy_name}.json
    Creates output_dir if needed.
    """
    output_dir.mkdir(parents=True, exist_ok=True)
    return output_dir / f"results_{strategy_name}.json"
