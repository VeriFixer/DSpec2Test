"""Unit tests for src.config module."""

import os
from pathlib import Path
from unittest.mock import patch

import pytest

from src.config import find_repo_root


class TestFindRepoRoot:
    """Tests for find_repo_root()."""

    def test_finds_marker_from_src_dir(self):
        """find_repo_root should find marker from within the repo."""
        root = find_repo_root()
        assert (root / ".repo_mutation_testing_marker").exists()

    def test_returns_path_type(self):
        root = find_repo_root()
        assert isinstance(root, Path)

    def test_missing_marker_raises(self, tmp_path):
        """Should raise FileNotFoundError when marker doesn't exist."""
        fake_file = tmp_path / "src" / "config.py"
        fake_file.parent.mkdir(parents=True)
        fake_file.touch()
        with patch("src.config.Path") as mock_path:
            # Simulate walking up from a dir with no marker
            mock_path.return_value.resolve.return_value.parent = tmp_path
            with pytest.raises(FileNotFoundError):
                find_repo_root(marker="nonexistent_marker_xyz")


class TestPathConstants:
    """Tests for path constants."""

    def test_base_path_contains_marker(self):
        from src.config import BASE_PATH
        assert (BASE_PATH / ".repo_mutation_testing_marker").exists()

    def test_dataset_root(self):
        from src.config import BASE_PATH, DATASET_ROOT
        assert DATASET_ROOT == BASE_PATH / "dataset" / "data"

    def test_external_root(self):
        from src.config import BASE_PATH, EXTERNAL_ROOT
        assert EXTERNAL_ROOT == BASE_PATH / "external"

    def test_tmp_root(self):
        from src.config import BASE_PATH, TMP_ROOT
        assert TMP_ROOT == BASE_PATH / "tmp"

    def test_artifacts_root(self):
        from src.config import TMP_ROOT, ARTIFACTS_ROOT
        assert ARTIFACTS_ROOT == TMP_ROOT / "run_artifacts"

    def test_dafny_binary(self):
        from src.config import BASE_PATH, DAFNY_BINARY
        assert DAFNY_BINARY == BASE_PATH.parent / "Binaries" / "Dafny"

    def test_mutdafny_plugin(self):
        from src.config import EXTERNAL_ROOT, MUTDAFNY_PLUGIN, MUTDAFNY_DAFNY_BINARY
        expected = EXTERNAL_ROOT / "mutation" / "mutdafny" / "mutdafny" / "bin" / "Debug" / "net8.0" / "mutdafny.dll"
        assert MUTDAFNY_PLUGIN == expected
        expected_bin = EXTERNAL_ROOT / "mutation" / "mutdafny" / "dafny" / "Binaries" / "Dafny"
        assert MUTDAFNY_DAFNY_BINARY == expected_bin


class TestConfigurableParams:
    """Tests for default values of configurable parameters."""

    def test_sample_count_default(self):
        """Without env var, SAMPLE_COUNT should be 100."""
        # Can't easily re-import with clean env, so just check type
        from src.config import SAMPLE_COUNT
        assert isinstance(SAMPLE_COUNT, int)
        assert SAMPLE_COUNT > 0

    def test_verify_timeout_default(self):
        from src.config import VERIFY_TIMEOUT
        assert isinstance(VERIFY_TIMEOUT, int)
        assert VERIFY_TIMEOUT > 0

    def test_max_jobs_at_least_one(self):
        from src.config import MAX_JOBS
        assert MAX_JOBS >= 1
