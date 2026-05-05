"""Unit tests for KillChecker."""

import subprocess
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

from src.mt_eval.execution.kill_checker import KillChecker, _derive_original_name
from src.mt_eval.core.models import MutantStatus


# --- _derive_original_name tests ---


class TestDeriveOriginalName:
    def test_standard_mutant_name(self):
        assert _derive_original_name("abs__161-188_CBE.dfy") == "abs.dfy"

    def test_no_double_underscore_fallback(self):
        assert _derive_original_name("plain.dfy") == "plain.dfy"

    def test_multiple_double_underscores(self):
        # Takes everything before the first '__'
        assert _derive_original_name("foo__bar__baz.dfy") == "foo.dfy"

    def test_complex_original_stem(self):
        assert _derive_original_name("my_program__10-20_AOR.dfy") == "my_program.dfy"


# --- KillChecker tests ---


class TestKillChecker:
    """Tests for check_kill using mocked subprocess and file I/O."""

    def _setup_file_mocks(self, mock_path_cls=None):
        """Helper: patch Path.read_text and Path.write_text and Path.mkdir."""
        pass  # We use tmp_path fixture instead

    @patch("src.mt_eval.execution.kill_checker.subprocess.run")
    def test_nonzero_exit_means_killed(self, mock_run, tmp_path):
        mock_run.return_value = MagicMock(returncode=1)

        # Setup file structure: dataset_dir/tests/test.dfy, dataset_dir/original/abs.dfy
        dataset_dir = tmp_path / "dataset"
        tests_dir = dataset_dir / "tests"
        original_dir = dataset_dir / "original"
        tests_dir.mkdir(parents=True)
        original_dir.mkdir(parents=True)

        original_file = original_dir / "abs.dfy"
        original_file.write_text("// original\n")

        test_file = tests_dir / "test.dfy"
        test_file.write_text("// original\n\nmethod {:test} T() {}\n")

        mutant_file = tmp_path / "abs__1-5_CBE.dfy"
        mutant_file.write_text("// mutant code\n")

        checker = KillChecker(timeout=10)
        result = checker.check_kill(test_file, mutant_file)
        assert result.status == MutantStatus.KILLED
        assert result.mutant_name == "abs__1-5_CBE.dfy"
        assert result.original_name == "abs.dfy"
        assert result.execution_time >= 0

    @patch("src.mt_eval.execution.kill_checker.subprocess.run")
    def test_zero_exit_means_survived(self, mock_run, tmp_path):
        mock_run.return_value = MagicMock(returncode=0)

        dataset_dir = tmp_path / "dataset"
        tests_dir = dataset_dir / "tests"
        original_dir = dataset_dir / "original"
        tests_dir.mkdir(parents=True)
        original_dir.mkdir(parents=True)

        original_file = original_dir / "prog.dfy"
        original_file.write_text("// original\n")

        test_file = tests_dir / "test.dfy"
        test_file.write_text("// original\n\nmethod {:test} T() {}\n")

        mutant_file = tmp_path / "prog__10-20_AOR.dfy"
        mutant_file.write_text("// mutant\n")

        checker = KillChecker(timeout=10)
        result = checker.check_kill(test_file, mutant_file)
        assert result.status == MutantStatus.SURVIVED
        assert result.original_name == "prog.dfy"

    @patch("src.mt_eval.execution.kill_checker.subprocess.run")
    def test_timeout_expired(self, mock_run, tmp_path):
        mock_run.side_effect = subprocess.TimeoutExpired(cmd="dafny", timeout=10)

        dataset_dir = tmp_path / "dataset"
        tests_dir = dataset_dir / "tests"
        original_dir = dataset_dir / "original"
        tests_dir.mkdir(parents=True)
        original_dir.mkdir(parents=True)

        original_file = original_dir / "abs.dfy"
        original_file.write_text("// original\n")

        test_file = tests_dir / "test.dfy"
        test_file.write_text("// original\n\nmethod {:test} T() {}\n")

        mutant_file = tmp_path / "abs__1-5_CBE.dfy"
        mutant_file.write_text("// mutant\n")

        checker = KillChecker(timeout=10)
        result = checker.check_kill(test_file, mutant_file)
        assert result.status == MutantStatus.TIMEOUT

    @patch("src.mt_eval.execution.kill_checker.subprocess.run")
    def test_other_exception_means_error(self, mock_run, tmp_path):
        mock_run.side_effect = OSError("binary not found")

        dataset_dir = tmp_path / "dataset"
        tests_dir = dataset_dir / "tests"
        original_dir = dataset_dir / "original"
        tests_dir.mkdir(parents=True)
        original_dir.mkdir(parents=True)

        original_file = original_dir / "abs.dfy"
        original_file.write_text("// original\n")

        test_file = tests_dir / "test.dfy"
        test_file.write_text("// original\n\nmethod {:test} T() {}\n")

        mutant_file = tmp_path / "abs__1-5_CBE.dfy"
        mutant_file.write_text("// mutant\n")

        checker = KillChecker(timeout=10)
        result = checker.check_kill(test_file, mutant_file)
        assert result.status == MutantStatus.ERROR

    @patch("src.mt_eval.execution.kill_checker.subprocess.run")
    def test_subprocess_called_with_allow_warnings(self, mock_run, tmp_path):
        """Verify --allow-warnings is in the dafny run command."""
        mock_run.return_value = MagicMock(returncode=0)

        dataset_dir = tmp_path / "dataset"
        tests_dir = dataset_dir / "tests"
        original_dir = dataset_dir / "original"
        tests_dir.mkdir(parents=True)
        original_dir.mkdir(parents=True)

        original_file = original_dir / "m.dfy"
        original_file.write_text("// orig\n")

        test_file = tests_dir / "test.dfy"
        test_file.write_text("// orig\n\nmethod {:test} T() {}\n")

        mutant_file = tmp_path / "m.dfy"
        mutant_file.write_text("// mutant\n")

        checker = KillChecker(timeout=42)
        checker.check_kill(test_file, mutant_file)

        call_args = mock_run.call_args
        cmd = call_args[0][0]
        assert cmd[0] == str(checker.dafny_binary)
        assert cmd[1] == "run"
        assert "--no-verify" in cmd
        assert "--allow-warnings" in cmd
        assert call_args[1]["timeout"] == 42

    @patch("src.mt_eval.execution.kill_checker.subprocess.run")
    def test_execution_time_positive(self, mock_run, tmp_path):
        mock_run.return_value = MagicMock(returncode=0)

        dataset_dir = tmp_path / "dataset"
        tests_dir = dataset_dir / "tests"
        original_dir = dataset_dir / "original"
        tests_dir.mkdir(parents=True)
        original_dir.mkdir(parents=True)

        original_file = original_dir / "x.dfy"
        original_file.write_text("// orig\n")

        test_file = tests_dir / "test.dfy"
        test_file.write_text("// orig\n\nmethod {:test} T() {}\n")

        mutant_file = tmp_path / "x__1-2_Y.dfy"
        mutant_file.write_text("// mutant\n")

        checker = KillChecker(timeout=10)
        result = checker.check_kill(test_file, mutant_file)
        assert result.execution_time >= 0

    @patch("src.mt_eval.execution.kill_checker.subprocess.run")
    def test_output_dir_used_when_set(self, mock_run, tmp_path):
        """When output_dir is set, combined file goes there instead of kill_tests/."""
        mock_run.return_value = MagicMock(returncode=0)

        dataset_dir = tmp_path / "dataset"
        tests_dir = dataset_dir / "tests"
        original_dir = dataset_dir / "original"
        tests_dir.mkdir(parents=True)
        original_dir.mkdir(parents=True)

        original_file = original_dir / "prog.dfy"
        original_file.write_text("// orig\n")

        test_file = tests_dir / "test.dfy"
        test_file.write_text("// orig\n\nmethod {:test} T() {}\n")

        mutant_file = tmp_path / "prog__1-2_X.dfy"
        mutant_file.write_text("// mutant content\n")

        custom_output = tmp_path / "custom_output"
        checker = KillChecker(timeout=10, output_dir=custom_output)
        checker.check_kill(test_file, mutant_file)

        # Combined file should be in custom_output, not kill_tests
        assert (custom_output / "prog__1-2_X.test.dfy").exists()
        assert not (dataset_dir / "kill_tests").exists()

    @patch("src.mt_eval.execution.kill_checker.subprocess.run")
    def test_default_output_dir_is_kill_tests(self, mock_run, tmp_path):
        """When output_dir is None (default), combined file goes to kill_tests/."""
        mock_run.return_value = MagicMock(returncode=0)

        dataset_dir = tmp_path / "dataset"
        tests_dir = dataset_dir / "tests"
        original_dir = dataset_dir / "original"
        tests_dir.mkdir(parents=True)
        original_dir.mkdir(parents=True)

        original_file = original_dir / "prog.dfy"
        original_file.write_text("// orig\n")

        test_file = tests_dir / "test.dfy"
        test_file.write_text("// orig\n\nmethod {:test} T() {}\n")

        mutant_file = tmp_path / "prog__1-2_X.dfy"
        mutant_file.write_text("// mutant content\n")

        checker = KillChecker(timeout=10)  # no output_dir
        checker.check_kill(test_file, mutant_file)

        # Combined file should be in dataset_dir/kill_tests/
        assert (dataset_dir / "kill_tests" / "prog__1-2_X.test.dfy").exists()


# --- Property-Based Tests (Hypothesis) ---
# Property 5: Kill classification matches exit code
# **Validates: Requirements 5.3, 5.4**


from hypothesis import given, settings
from hypothesis import strategies as st


class TestKillClassificationProperty:
    """Property 5: Kill classification matches exit code.

    For any kill check execution, if dafny run --no-verify returns non-zero
    the mutant SHALL be classified as killed, and if it returns zero the
    mutant SHALL be classified as survived.

    **Validates: Requirements 5.3, 5.4**
    """

    @given(exit_code=st.integers(min_value=1, max_value=255))
    @settings(max_examples=100)
    def test_nonzero_exit_code_means_killed(self, exit_code, tmp_path_factory):
        """Any non-zero exit code → KILLED.

        **Validates: Requirements 5.3**
        """
        tmp_path = tmp_path_factory.mktemp("kill")

        dataset_dir = tmp_path / "dataset"
        tests_dir = dataset_dir / "tests"
        original_dir = dataset_dir / "original"
        tests_dir.mkdir(parents=True)
        original_dir.mkdir(parents=True)

        original_file = original_dir / "prog.dfy"
        original_file.write_text("// original\n")

        test_file = tests_dir / "test.dfy"
        test_file.write_text("// original\n\nmethod {:test} T() {}\n")

        mutant_file = tmp_path / "prog__1-5_CBE.dfy"
        mutant_file.write_text("// mutant\n")

        with patch("src.mt_eval.execution.kill_checker.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(returncode=exit_code)
            checker = KillChecker(timeout=10)
            result = checker.check_kill(test_file, mutant_file)

        assert result.status == MutantStatus.KILLED

    @given(exit_code=st.just(0))
    @settings(max_examples=100)
    def test_zero_exit_code_means_survived(self, exit_code, tmp_path_factory):
        """Exit code 0 → SURVIVED.

        **Validates: Requirements 5.4**
        """
        tmp_path = tmp_path_factory.mktemp("surv")

        dataset_dir = tmp_path / "dataset"
        tests_dir = dataset_dir / "tests"
        original_dir = dataset_dir / "original"
        tests_dir.mkdir(parents=True)
        original_dir.mkdir(parents=True)

        original_file = original_dir / "prog.dfy"
        original_file.write_text("// original\n")

        test_file = tests_dir / "test.dfy"
        test_file.write_text("// original\n\nmethod {:test} T() {}\n")

        mutant_file = tmp_path / "prog__1-5_CBE.dfy"
        mutant_file.write_text("// mutant\n")

        with patch("src.mt_eval.execution.kill_checker.subprocess.run") as mock_run:
            mock_run.return_value = MagicMock(returncode=exit_code)
            checker = KillChecker(timeout=10)
            result = checker.check_kill(test_file, mutant_file)

        assert result.status == MutantStatus.SURVIVED
