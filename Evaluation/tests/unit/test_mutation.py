"""Unit tests for src.mt_eval.core.mutation module."""

from pathlib import Path
from unittest.mock import patch, MagicMock, call
import subprocess

import pytest

from src.mt_eval.core.mutation import apply_mutation, generate_diff


class TestApplyMutation:
    """Tests for apply_mutation function."""

    @patch("src.mt_eval.core.mutation.tempfile.TemporaryDirectory")
    @patch("src.mt_eval.core.mutation.subprocess.run")
    def test_returns_first_mutant_on_success(self, mock_run, mock_tmpdir, tmp_path):
        """Scan produces targets, mutation produces a .dfy file."""
        work_dir = tmp_path / "work"
        work_dir.mkdir()
        mock_tmpdir.return_value.__enter__ = MagicMock(return_value=str(work_dir))
        mock_tmpdir.return_value.__exit__ = MagicMock(return_value=False)

        # First call = scan (creates targets.csv)
        def side_effect(*args, **kwargs):
            cmd = args[0]
            plugin_str = [c for c in cmd if "--plugin:" in c][0]
            if "scan" in plugin_str:
                (work_dir / "targets.csv").write_text("1,BinaryOp,\n")
            else:
                # Mutation pass produces a .dfy file
                (work_dir / "prog_mut.dfy").write_text("mutant code")
            return MagicMock(returncode=0)

        mock_run.side_effect = side_effect
        out_dir = tmp_path / "mutants"

        result = apply_mutation(Path("/some/prog.dfy"), out_dir)

        assert len(result) == 1
        assert result[0].suffix == ".dfy"
        assert result[0].parent == out_dir
        assert result[0].read_text() == "mutant code"

    @patch("src.mt_eval.core.mutation.tempfile.TemporaryDirectory")
    @patch("src.mt_eval.core.mutation.subprocess.run")
    def test_returns_empty_on_scan_failure(self, mock_run, mock_tmpdir, tmp_path):
        """Scan pass fails (timeout)."""
        work_dir = tmp_path / "work"
        work_dir.mkdir()
        mock_tmpdir.return_value.__enter__ = MagicMock(return_value=str(work_dir))
        mock_tmpdir.return_value.__exit__ = MagicMock(return_value=False)

        mock_run.side_effect = subprocess.TimeoutExpired(cmd="dafny", timeout=300)
        out_dir = tmp_path / "mutants"

        result = apply_mutation(Path("prog.dfy"), out_dir)
        assert result == []

    @patch("src.mt_eval.core.mutation.tempfile.TemporaryDirectory")
    @patch("src.mt_eval.core.mutation.subprocess.run")
    def test_returns_empty_on_os_error(self, mock_run, mock_tmpdir, tmp_path):
        """Dafny binary not found."""
        work_dir = tmp_path / "work"
        work_dir.mkdir()
        mock_tmpdir.return_value.__enter__ = MagicMock(return_value=str(work_dir))
        mock_tmpdir.return_value.__exit__ = MagicMock(return_value=False)

        mock_run.side_effect = OSError("No such file")
        out_dir = tmp_path / "mutants"

        result = apply_mutation(Path("prog.dfy"), out_dir)
        assert result == []

    @patch("src.mt_eval.core.mutation.tempfile.TemporaryDirectory")
    @patch("src.mt_eval.core.mutation.subprocess.run")
    def test_returns_empty_when_no_targets(self, mock_run, mock_tmpdir, tmp_path):
        """Scan succeeds but targets.csv is empty."""
        work_dir = tmp_path / "work"
        work_dir.mkdir()
        mock_tmpdir.return_value.__enter__ = MagicMock(return_value=str(work_dir))
        mock_tmpdir.return_value.__exit__ = MagicMock(return_value=False)

        # Scan succeeds, creates empty targets.csv
        (work_dir / "targets.csv").write_text("")
        mock_run.return_value = MagicMock(returncode=0)
        out_dir = tmp_path / "mutants"

        result = apply_mutation(Path("prog.dfy"), out_dir)
        assert result == []

    @patch("src.mt_eval.core.mutation.tempfile.TemporaryDirectory")
    @patch("src.mt_eval.core.mutation.subprocess.run")
    def test_returns_empty_when_no_mutants_produced(self, mock_run, mock_tmpdir, tmp_path):
        """Mutation pass runs but produces no .dfy files."""
        work_dir = tmp_path / "work"
        work_dir.mkdir()
        mock_tmpdir.return_value.__enter__ = MagicMock(return_value=str(work_dir))
        mock_tmpdir.return_value.__exit__ = MagicMock(return_value=False)

        call_count = [0]

        def side_effect(*args, **kwargs):
            call_count[0] += 1
            if call_count[0] == 1:
                # Scan pass
                (work_dir / "targets.csv").write_text("1,BinaryOp,\n2,StmtDel,\n")
            # No .dfy files produced by mutation passes
            return MagicMock(returncode=0)

        mock_run.side_effect = side_effect
        out_dir = tmp_path / "mutants"

        result = apply_mutation(Path("prog.dfy"), out_dir)
        assert result == []

    @patch("src.mt_eval.core.mutation.tempfile.TemporaryDirectory")
    @patch("src.mt_eval.core.mutation.subprocess.run")
    def test_creates_output_dir_if_missing(self, mock_run, mock_tmpdir, tmp_path):
        """output_dir is created if it doesn't exist."""
        work_dir = tmp_path / "work"
        work_dir.mkdir()
        mock_tmpdir.return_value.__enter__ = MagicMock(return_value=str(work_dir))
        mock_tmpdir.return_value.__exit__ = MagicMock(return_value=False)

        mock_run.side_effect = OSError("No such file")
        out_dir = tmp_path / "new" / "nested" / "dir"

        apply_mutation(Path("prog.dfy"), out_dir)
        assert out_dir.exists()

    @patch("src.mt_eval.core.mutation.tempfile.TemporaryDirectory")
    @patch("src.mt_eval.core.mutation.subprocess.run")
    def test_passes_plugin_arg_with_three_fields(self, mock_run, mock_tmpdir, tmp_path):
        """When target has pos, op, and arg, all three are passed."""
        work_dir = tmp_path / "work"
        work_dir.mkdir()
        mock_tmpdir.return_value.__enter__ = MagicMock(return_value=str(work_dir))
        mock_tmpdir.return_value.__exit__ = MagicMock(return_value=False)

        call_count = [0]

        def side_effect(*args, **kwargs):
            call_count[0] += 1
            if call_count[0] == 1:
                (work_dir / "targets.csv").write_text("5,BinaryOp,>=\n")
            return MagicMock(returncode=0)

        mock_run.side_effect = side_effect
        out_dir = tmp_path / "mutants"

        apply_mutation(Path("prog.dfy"), out_dir)

        # Second call should have "mut 5 BinaryOp >="
        second_call = mock_run.call_args_list[1][0][0]
        plugin_args = [c for c in second_call if "--plugin:" in c]
        assert len(plugin_args) == 1
        assert "mut 5 BinaryOp >=" in plugin_args[0]


class TestGenerateDiff:
    """Tests for generate_diff function."""

    def test_produces_diff_file(self, tmp_path):
        """Diff file is created with unified diff content."""
        orig = tmp_path / "original.dfy"
        mutant = tmp_path / "mutant.dfy"
        diff_out = tmp_path / "output.txt"

        orig.write_text("line1\nline2\nline3\n")
        mutant.write_text("line1\nchanged\nline3\n")

        result = generate_diff(orig, mutant, diff_out)

        assert result == diff_out
        assert diff_out.exists()
        content = diff_out.read_text()
        assert "---" in content
        assert "+++" in content
        assert "-line2" in content
        assert "+changed" in content

    def test_returns_output_path(self, tmp_path):
        """Return value is the output_path."""
        orig = tmp_path / "a.dfy"
        mutant = tmp_path / "b.dfy"
        diff_out = tmp_path / "diff.txt"

        orig.write_text("same\n")
        mutant.write_text("same\n")

        result = generate_diff(orig, mutant, diff_out)
        assert result == diff_out

    def test_identical_files_produce_empty_diff(self, tmp_path):
        """No differences means empty diff content."""
        orig = tmp_path / "a.dfy"
        mutant = tmp_path / "b.dfy"
        diff_out = tmp_path / "diff.txt"

        orig.write_text("line1\nline2\n")
        mutant.write_text("line1\nline2\n")

        generate_diff(orig, mutant, diff_out)
        assert diff_out.read_text() == ""

    def test_creates_parent_dirs(self, tmp_path):
        """Output path parent dirs created if missing."""
        orig = tmp_path / "a.dfy"
        mutant = tmp_path / "b.dfy"
        diff_out = tmp_path / "nested" / "deep" / "diff.txt"

        orig.write_text("x\n")
        mutant.write_text("y\n")

        generate_diff(orig, mutant, diff_out)
        assert diff_out.exists()

    def test_diff_contains_file_names(self, tmp_path):
        """Diff header includes original and mutant file paths."""
        orig = tmp_path / "original.dfy"
        mutant = tmp_path / "mutant.dfy"
        diff_out = tmp_path / "diff.txt"

        orig.write_text("a\n")
        mutant.write_text("b\n")

        generate_diff(orig, mutant, diff_out)
        content = diff_out.read_text()
        assert str(orig) in content
        assert str(mutant) in content
