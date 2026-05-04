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
    """Tests for check_kill using mocked subprocess."""

    @patch("src.mt_eval.execution.kill_checker.subprocess.run")
    def test_nonzero_exit_means_killed(self, mock_run):
        mock_run.return_value = MagicMock(returncode=1)
        checker = KillChecker(timeout=10)
        result = checker.check_kill(
            Path("/tmp/test.dfy"), Path("/tmp/abs__1-5_CBE.dfy")
        )
        assert result.status == MutantStatus.KILLED
        assert result.mutant_name == "abs__1-5_CBE.dfy"
        assert result.original_name == "abs.dfy"
        assert result.execution_time >= 0

    @patch("src.mt_eval.execution.kill_checker.subprocess.run")
    def test_zero_exit_means_survived(self, mock_run):
        mock_run.return_value = MagicMock(returncode=0)
        checker = KillChecker(timeout=10)
        result = checker.check_kill(
            Path("/tmp/test.dfy"), Path("/tmp/prog__10-20_AOR.dfy")
        )
        assert result.status == MutantStatus.SURVIVED
        assert result.original_name == "prog.dfy"

    @patch("src.mt_eval.execution.kill_checker.subprocess.run")
    def test_timeout_expired(self, mock_run):
        mock_run.side_effect = subprocess.TimeoutExpired(cmd="dafny", timeout=10)
        checker = KillChecker(timeout=10)
        result = checker.check_kill(
            Path("/tmp/test.dfy"), Path("/tmp/abs__1-5_CBE.dfy")
        )
        assert result.status == MutantStatus.TIMEOUT

    @patch("src.mt_eval.execution.kill_checker.subprocess.run")
    def test_other_exception_means_error(self, mock_run):
        mock_run.side_effect = OSError("binary not found")
        checker = KillChecker(timeout=10)
        result = checker.check_kill(
            Path("/tmp/test.dfy"), Path("/tmp/abs__1-5_CBE.dfy")
        )
        assert result.status == MutantStatus.ERROR

    @patch("src.mt_eval.execution.kill_checker.subprocess.run")
    def test_subprocess_called_with_correct_args(self, mock_run):
        mock_run.return_value = MagicMock(returncode=0)
        checker = KillChecker(timeout=42)
        test_file = Path("/tmp/test.dfy")
        mutant_file = Path("/tmp/m.dfy")
        checker.check_kill(test_file, mutant_file)

        mock_run.assert_called_once_with(
            [str(checker.dafny_binary), "run", "--no-verify", str(test_file)],
            capture_output=True,
            timeout=42,
        )

    @patch("src.mt_eval.execution.kill_checker.subprocess.run")
    def test_execution_time_positive(self, mock_run):
        mock_run.return_value = MagicMock(returncode=0)
        checker = KillChecker(timeout=10)
        result = checker.check_kill(
            Path("/tmp/test.dfy"), Path("/tmp/x__1-2_Y.dfy")
        )
        assert result.execution_time >= 0
