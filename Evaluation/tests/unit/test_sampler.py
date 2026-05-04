"""Unit tests for sampler module."""

import logging
from pathlib import Path

import pytest

from src.mt_eval.core.sampler import sample_programs

GT_REL = Path("DafnyBench") / "dataset" / "ground_truth"


@pytest.fixture
def dafnybench(tmp_path: Path) -> Path:
    """Create a fake DafnyBench dir with DafnyBench/dataset/ground_truth/*.dfy files."""
    gt = tmp_path / GT_REL
    gt.mkdir(parents=True)
    for i in range(10):
        (gt / f"prog_{i}.dfy").write_text(f"// program {i}")
    return tmp_path


class TestSamplePrograms:
    """Tests for sample_programs()."""

    def test_returns_n_distinct_files(self, dafnybench: Path) -> None:
        result = sample_programs(dafnybench, 5)
        assert len(result) == 5
        assert len(set(result)) == 5
        for p in result:
            assert p.suffix == ".dfy"

    def test_pool_smaller_than_n_returns_all(self, dafnybench: Path) -> None:
        result = sample_programs(dafnybench, 20)
        assert len(result) == 10  # only 10 files exist

    def test_pool_equal_to_n(self, dafnybench: Path) -> None:
        result = sample_programs(dafnybench, 10)
        assert len(result) == 10
        assert len(set(result)) == 10

    def test_n_zero_returns_empty(self, dafnybench: Path) -> None:
        result = sample_programs(dafnybench, 0)
        assert result == []

    def test_empty_ground_truth(self, tmp_path: Path) -> None:
        gt = tmp_path / GT_REL
        gt.mkdir(parents=True)
        result = sample_programs(tmp_path, 5)
        assert result == []

    def test_no_ground_truth_dir(self, tmp_path: Path) -> None:
        result = sample_programs(tmp_path, 5)
        assert result == []

    def test_warns_when_pool_smaller(self, dafnybench: Path, caplog) -> None:
        with caplog.at_level(logging.WARNING):
            sample_programs(dafnybench, 20)
        assert "Pool size" in caplog.text

    def test_recursive_glob(self, tmp_path: Path) -> None:
        """Files in subdirs of ground_truth are found."""
        gt = tmp_path / GT_REL / "subdir"
        gt.mkdir(parents=True)
        for i in range(3):
            (gt / f"nested_{i}.dfy").write_text(f"// nested {i}")
        result = sample_programs(tmp_path, 3)
        assert len(result) == 3

    def test_all_returned_paths_exist(self, dafnybench: Path) -> None:
        result = sample_programs(dafnybench, 5)
        for p in result:
            assert p.exists()

    def test_same_seed_same_result(self, dafnybench: Path) -> None:
        """Same seed produces identical samples."""
        r1 = sample_programs(dafnybench, 5, seed=123)
        r2 = sample_programs(dafnybench, 5, seed=123)
        assert r1 == r2

    def test_different_seed_different_result(self, dafnybench: Path) -> None:
        """Different seeds produce different samples (with high probability)."""
        r1 = sample_programs(dafnybench, 5, seed=1)
        r2 = sample_programs(dafnybench, 5, seed=2)
        assert r1 != r2
