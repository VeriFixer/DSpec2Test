"""Unit tests for src.mt_eval.core.verification module."""

from pathlib import Path
from unittest.mock import patch, MagicMock
import subprocess

import pytest

from src.mt_eval.core.verification import verify_program, filter_verified


class TestVerifyProgram:
    """Tests for verify_program function."""

    @patch("src.mt_eval.core.verification.subprocess.run")
    def test_returns_true_on_exit_zero(self, mock_run):
        mock_run.return_value = MagicMock(returncode=0)
        assert verify_program(Path("good.dfy")) is True

    @patch("src.mt_eval.core.verification.subprocess.run")
    def test_returns_false_on_nonzero_exit(self, mock_run):
        mock_run.return_value = MagicMock(returncode=1)
        assert verify_program(Path("bad.dfy")) is False

    @patch("src.mt_eval.core.verification.subprocess.run")
    def test_returns_false_on_timeout(self, mock_run):
        mock_run.side_effect = subprocess.TimeoutExpired(cmd="dafny", timeout=300)
        assert verify_program(Path("slow.dfy")) is False

    @patch("src.mt_eval.core.verification.subprocess.run")
    def test_calls_dafny_with_correct_args(self, mock_run):
        mock_run.return_value = MagicMock(returncode=0)
        dafny_file = Path("/some/file.dfy")
        verify_program(dafny_file)

        call_args = mock_run.call_args
        cmd = call_args[0][0]
        assert "verify" in cmd
        assert "--allow-warnings" in cmd
        assert str(dafny_file) in cmd


class TestFilterVerified:
    """Tests for filter_verified function."""

    @patch("src.mt_eval.core.verification.run_parallel_or_seq")
    def test_all_pass(self, mock_parallel):
        files = [Path("a.dfy"), Path("b.dfy"), Path("c.dfy")]
        mock_parallel.return_value = [True, True, True]

        passed, pass_count, fail_count = filter_verified(files)

        assert passed == files
        assert pass_count == 3
        assert fail_count == 0

    @patch("src.mt_eval.core.verification.run_parallel_or_seq")
    def test_all_fail(self, mock_parallel):
        files = [Path("a.dfy"), Path("b.dfy")]
        mock_parallel.return_value = [False, False]

        passed, pass_count, fail_count = filter_verified(files)

        assert passed == []
        assert pass_count == 0
        assert fail_count == 2

    @patch("src.mt_eval.core.verification.run_parallel_or_seq")
    def test_mixed_results(self, mock_parallel):
        files = [Path("a.dfy"), Path("b.dfy"), Path("c.dfy")]
        mock_parallel.return_value = [True, False, True]

        passed, pass_count, fail_count = filter_verified(files)

        assert passed == [Path("a.dfy"), Path("c.dfy")]
        assert pass_count == 2
        assert fail_count == 1

    @patch("src.mt_eval.core.verification.run_parallel_or_seq")
    def test_empty_input(self, mock_parallel):
        mock_parallel.return_value = []

        passed, pass_count, fail_count = filter_verified([])

        assert passed == []
        assert pass_count == 0
        assert fail_count == 0

    @patch("src.mt_eval.core.verification.run_parallel_or_seq")
    def test_counts_sum_to_total(self, mock_parallel):
        files = [Path(f"{i}.dfy") for i in range(5)]
        mock_parallel.return_value = [True, False, True, False, True]

        passed, pass_count, fail_count = filter_verified(files)

        assert pass_count + fail_count == len(files)

    @patch("src.mt_eval.core.verification.run_parallel_or_seq")
    def test_parallel_flag_forwarded(self, mock_parallel):
        mock_parallel.return_value = []

        filter_verified([], parallel=False)
        _, kwargs = mock_parallel.call_args
        assert kwargs["parallel"] is False

        filter_verified([], parallel=True)
        _, kwargs = mock_parallel.call_args
        assert kwargs["parallel"] is True
