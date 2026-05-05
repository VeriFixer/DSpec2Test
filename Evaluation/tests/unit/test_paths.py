"""Unit tests for per-strategy path derivation (src.mt_eval.paths)."""

from pathlib import Path

from src.mt_eval.paths import get_strategy_combined_dir, get_strategy_results_path


def test_combined_dir_uses_mode(tmp_path: Path) -> None:
    """Combined dir includes mode in name."""
    result = get_strategy_combined_dir("Spec", base_path=tmp_path)
    assert result == tmp_path / "dataset" / "selected_programs_mutants_with_tests_Spec"


def test_combined_dir_creates_directory(tmp_path: Path) -> None:
    """Combined dir is created if it doesn't exist."""
    result = get_strategy_combined_dir("Block", base_path=tmp_path)
    assert result.is_dir()


def test_combined_dir_idempotent(tmp_path: Path) -> None:
    """Calling twice doesn't error."""
    d1 = get_strategy_combined_dir("Spec", base_path=tmp_path)
    d2 = get_strategy_combined_dir("Spec", base_path=tmp_path)
    assert d1 == d2


def test_results_path_uses_strategy_name(tmp_path: Path) -> None:
    """Results path includes strategy name."""
    result = get_strategy_results_path("DafnyTestGenerator_Spec", tmp_path)
    assert result == tmp_path / "results_DafnyTestGenerator_Spec.json"


def test_results_path_creates_output_dir(tmp_path: Path) -> None:
    """Output dir is created if missing."""
    out = tmp_path / "nested" / "results"
    result = get_strategy_results_path("foo", out)
    assert out.is_dir()
    assert result.name == "results_foo.json"
