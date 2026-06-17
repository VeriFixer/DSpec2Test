"""Per-strategy path derivation utilities.

Derives output directories and results file paths from strategy mode/name.
"""

from pathlib import Path

from src.config import BASE_PATH, DATASET_OUTPUT_DIR


def get_strategy_combined_dir(mode: str, base_path: Path | None = None) -> Path:
    """Return per-strategy combined test+mutant directory, creating it if needed.

    Path: base_path / dataset_output / selected_programs_mutants_with_tests_{mode}/
    """
    root = base_path if base_path is not None else BASE_PATH
    combined_dir = root / DATASET_OUTPUT_DIR / f"selected_programs_mutants_with_tests_{mode}"
    combined_dir.mkdir(parents=True, exist_ok=True)
    return combined_dir


def get_strategy_tests_dir(mode: str, base_path: Path | None = None) -> Path:
    """Return the directory containing the raw generated tests for the original programs."""
    root = base_path if base_path is not None else BASE_PATH
    tests_dir = root / DATASET_OUTPUT_DIR / f"tests_{mode}" 
    tests_dir.mkdir(parents=True, exist_ok=True)
    return tests_dir


def get_strategy_tmp_exec_dir(combined_dir: Path) -> Path:
    """Return the temporary execution directory for split tests."""
    tmp_dir = combined_dir / ".tmp_execution"
    tmp_dir.mkdir(parents=True, exist_ok=True)
    return tmp_dir


def get_strategy_debug_dir(combined_dir: Path) -> Path:
    """Return the debug artifacts directory for safety and kill check failures."""
    debug_dir = combined_dir / "debug_artifacts"
    debug_dir.mkdir(parents=True, exist_ok=True)
    return debug_dir


def get_strategy_all_dir(combined_dir: Path) -> Path:
    """Return the final dataset directory containing all cumulative tests."""
    all_dir = combined_dir / "all"
    all_dir.mkdir(parents=True, exist_ok=True)
    return all_dir


def get_strategy_results_path(strategy_name: str, output_dir: Path) -> Path:
    """Return per-strategy results JSON path.

    Path: output_dir / results_{strategy_name}.json
    Creates output_dir if needed.
    """
    output_dir.mkdir(parents=True, exist_ok=True)
    return output_dir / f"results_{strategy_name}.json"
