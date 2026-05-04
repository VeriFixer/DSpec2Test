"""Unit tests for src.runners.generate_dataset module."""

from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

from src.runners.generate_dataset import parse_args, run_pipeline, main


class TestParseArgs:
    """Tests for CLI argument parsing."""

    def test_defaults(self):
        args = parse_args([])
        assert args.n_mutants == 100
        assert args.output_dir is None
        assert args.sequential is False

    def test_n_mutants(self):
        args = parse_args(["--n-mutants", "50"])
        assert args.n_mutants == 50

    def test_output_dir(self):
        args = parse_args(["--output-dir", "/tmp/out"])
        assert args.output_dir == "/tmp/out"

    def test_sequential(self):
        args = parse_args(["--sequential"])
        assert args.sequential is True

    def test_all_flags(self):
        args = parse_args(["--n-mutants", "10", "--output-dir", "out", "--sequential"])
        assert args.n_mutants == 10
        assert args.output_dir == "out"
        assert args.sequential is True


class TestRunPipeline:
    """Tests for run_pipeline function."""

    @patch("src.runners.generate_dataset.sample_programs")
    def test_returns_1_when_no_samples(self, mock_sample, tmp_path):
        """Empty sample → critical failure."""
        mock_sample.return_value = []
        result = run_pipeline(10, tmp_path / "out", sequential=False)
        assert result == 1

    @patch("src.runners.generate_dataset.filter_verified")
    @patch("src.runners.generate_dataset.sample_programs")
    def test_returns_1_when_none_verified(self, mock_sample, mock_filter, tmp_path):
        """All fail verification → critical failure."""
        mock_sample.return_value = [Path("a.dfy")]
        mock_filter.return_value = ([], 0, 1)
        result = run_pipeline(10, tmp_path / "out", sequential=False)
        assert result == 1

    @patch("src.runners.generate_dataset.generate_diff")
    @patch("src.runners.generate_dataset.verify_program")
    @patch("src.runners.generate_dataset.apply_mutation")
    @patch("src.runners.generate_dataset.filter_verified")
    @patch("src.runners.generate_dataset.sample_programs")
    def test_success_pipeline(
        self, mock_sample, mock_filter, mock_mutate, mock_verify_prog, mock_diff, tmp_path
    ):
        """Full success path: sample → verify → mutate → mutant fails verify → diff."""
        orig = tmp_path / "src" / "prog.dfy"
        orig.parent.mkdir(parents=True)
        orig.write_text("// original")

        mutant = tmp_path / "mut" / "prog__1-2_CBE.dfy"
        mutant.parent.mkdir(parents=True)
        mutant.write_text("// mutant")

        mock_sample.return_value = [orig]
        mock_filter.return_value = ([orig], 1, 0)
        mock_mutate.return_value = mutant
        mock_verify_prog.return_value = False  # mutant fails verification = good
        mock_diff.return_value = Path("diff.txt")

        out_dir = tmp_path / "out"
        result = run_pipeline(1, out_dir, sequential=False)

        assert result == 0
        assert (out_dir / "original").exists()
        assert (out_dir / "killed").exists()
        mock_diff.assert_called_once()

    @patch("src.runners.generate_dataset.verify_program")
    @patch("src.runners.generate_dataset.apply_mutation")
    @patch("src.runners.generate_dataset.filter_verified")
    @patch("src.runners.generate_dataset.sample_programs")
    def test_skips_when_mutation_fails(
        self, mock_sample, mock_filter, mock_mutate, mock_verify_prog, tmp_path
    ):
        """Mutation failure → skip file, return 1 if no valid mutants."""
        orig = tmp_path / "prog.dfy"
        orig.write_text("// original")

        mock_sample.return_value = [orig]
        mock_filter.return_value = ([orig], 1, 0)
        mock_mutate.return_value = None  # mutation fails

        result = run_pipeline(1, tmp_path / "out", sequential=False)
        assert result == 1  # no valid mutants

    @patch("src.runners.generate_dataset.verify_program")
    @patch("src.runners.generate_dataset.apply_mutation")
    @patch("src.runners.generate_dataset.filter_verified")
    @patch("src.runners.generate_dataset.sample_programs")
    def test_skips_when_mutant_still_verifies(
        self, mock_sample, mock_filter, mock_mutate, mock_verify_prog, tmp_path
    ):
        """Mutant that still verifies → skip (not a real bug)."""
        orig = tmp_path / "prog.dfy"
        orig.write_text("// original")

        mutant = tmp_path / "mut" / "prog__1-2_CBE.dfy"
        mutant.parent.mkdir(parents=True)
        mutant.write_text("// mutant")

        mock_sample.return_value = [orig]
        mock_filter.return_value = ([orig], 1, 0)
        mock_mutate.return_value = mutant
        mock_verify_prog.return_value = True  # mutant still verifies = bad

        result = run_pipeline(1, tmp_path / "out", sequential=False)
        assert result == 1  # no valid mutants

    @patch("src.runners.generate_dataset.generate_diff")
    @patch("src.runners.generate_dataset.verify_program")
    @patch("src.runners.generate_dataset.apply_mutation")
    @patch("src.runners.generate_dataset.filter_verified")
    @patch("src.runners.generate_dataset.sample_programs")
    def test_sequential_mode_prints_info(
        self, mock_sample, mock_filter, mock_mutate, mock_verify_prog, mock_diff, tmp_path, capsys
    ):
        """Sequential mode prints per-file debug info."""
        orig = tmp_path / "src" / "prog.dfy"
        orig.parent.mkdir(parents=True)
        orig.write_text("// original")

        mutant = tmp_path / "mut" / "prog__1-2_CBE.dfy"
        mutant.parent.mkdir(parents=True)
        mutant.write_text("// mutant")

        mock_sample.return_value = [orig]
        mock_filter.return_value = ([orig], 1, 0)
        mock_mutate.return_value = mutant
        mock_verify_prog.return_value = False
        mock_diff.return_value = Path("diff.txt")

        out_dir = tmp_path / "out"
        run_pipeline(1, out_dir, sequential=True)

        captured = capsys.readouterr()
        assert "[generate_dataset]" in captured.out
        assert "Sampling" in captured.out
        assert "prog.dfy" in captured.out

    @patch("src.runners.generate_dataset.generate_diff")
    @patch("src.runners.generate_dataset.verify_program")
    @patch("src.runners.generate_dataset.apply_mutation")
    @patch("src.runners.generate_dataset.filter_verified")
    @patch("src.runners.generate_dataset.sample_programs")
    def test_creates_output_dirs(
        self, mock_sample, mock_filter, mock_mutate, mock_verify_prog, mock_diff, tmp_path
    ):
        """Output dir with original/ and killed/ subdirs created."""
        orig = tmp_path / "src" / "prog.dfy"
        orig.parent.mkdir(parents=True)
        orig.write_text("// original")

        mutant = tmp_path / "mut" / "prog__1-2_CBE.dfy"
        mutant.parent.mkdir(parents=True)
        mutant.write_text("// mutant")

        mock_sample.return_value = [orig]
        mock_filter.return_value = ([orig], 1, 0)
        mock_mutate.return_value = mutant
        mock_verify_prog.return_value = False
        mock_diff.return_value = Path("diff.txt")

        out_dir = tmp_path / "out"
        run_pipeline(1, out_dir, sequential=False)

        assert (out_dir / "original").is_dir()
        assert (out_dir / "killed").is_dir()

    @patch("src.runners.generate_dataset.generate_diff")
    @patch("src.runners.generate_dataset.verify_program")
    @patch("src.runners.generate_dataset.apply_mutation")
    @patch("src.runners.generate_dataset.filter_verified")
    @patch("src.runners.generate_dataset.sample_programs")
    def test_copies_original_and_mutant(
        self, mock_sample, mock_filter, mock_mutate, mock_verify_prog, mock_diff, tmp_path
    ):
        """Original copied to original/, mutant to killed/."""
        orig = tmp_path / "src" / "prog.dfy"
        orig.parent.mkdir(parents=True)
        orig.write_text("// original content")

        mutant = tmp_path / "mut" / "prog__1-2_CBE.dfy"
        mutant.parent.mkdir(parents=True)
        mutant.write_text("// mutant content")

        mock_sample.return_value = [orig]
        mock_filter.return_value = ([orig], 1, 0)
        mock_mutate.return_value = mutant
        mock_verify_prog.return_value = False
        mock_diff.return_value = Path("diff.txt")

        out_dir = tmp_path / "out"
        run_pipeline(1, out_dir, sequential=False)

        assert (out_dir / "original" / "prog.dfy").read_text() == "// original content"
        assert (out_dir / "killed" / "prog__1-2_CBE.dfy").read_text() == "// mutant content"

    @patch("src.runners.generate_dataset.generate_diff")
    @patch("src.runners.generate_dataset.verify_program")
    @patch("src.runners.generate_dataset.apply_mutation")
    @patch("src.runners.generate_dataset.filter_verified")
    @patch("src.runners.generate_dataset.sample_programs")
    def test_cleans_up_tmp_mutants(
        self, mock_sample, mock_filter, mock_mutate, mock_verify_prog, mock_diff, tmp_path
    ):
        """Temp _tmp_mutants dir cleaned up after pipeline."""
        orig = tmp_path / "src" / "prog.dfy"
        orig.parent.mkdir(parents=True)
        orig.write_text("// original")

        mutant = tmp_path / "mut" / "prog__1-2_CBE.dfy"
        mutant.parent.mkdir(parents=True)
        mutant.write_text("// mutant")

        mock_sample.return_value = [orig]
        mock_filter.return_value = ([orig], 1, 0)
        mock_mutate.return_value = mutant
        mock_verify_prog.return_value = False
        mock_diff.return_value = Path("diff.txt")

        out_dir = tmp_path / "out"
        run_pipeline(1, out_dir, sequential=False)

        assert not (out_dir / "_tmp_mutants").exists()


class TestMain:
    """Tests for main() entry point."""

    @patch("src.runners.generate_dataset.run_pipeline")
    def test_main_calls_pipeline(self, mock_pipeline):
        """main() parses args and calls run_pipeline."""
        mock_pipeline.return_value = 0
        with pytest.raises(SystemExit) as exc_info:
            main(["--n-mutants", "5", "--output-dir", "/tmp/test"])
        assert exc_info.value.code == 0
        mock_pipeline.assert_called_once()
        call_kwargs = mock_pipeline.call_args
        assert call_kwargs[1]["n_mutants"] == 5

    @patch("src.runners.generate_dataset.run_pipeline")
    def test_main_exits_nonzero_on_failure(self, mock_pipeline):
        """main() exits non-zero when pipeline fails."""
        mock_pipeline.return_value = 1
        with pytest.raises(SystemExit) as exc_info:
            main(["--n-mutants", "5"])
        assert exc_info.value.code == 1

    @patch("src.runners.generate_dataset.run_pipeline")
    def test_main_default_output_dir(self, mock_pipeline):
        """Default output dir is 'dataset_output'."""
        mock_pipeline.return_value = 0
        with pytest.raises(SystemExit):
            main([])
        call_args = mock_pipeline.call_args
        assert call_args[1]["output_dir"] == Path("dataset_output")

    @patch("src.runners.generate_dataset.run_pipeline")
    def test_main_sequential_flag(self, mock_pipeline):
        """--sequential passed through."""
        mock_pipeline.return_value = 0
        with pytest.raises(SystemExit):
            main(["--sequential"])
        call_args = mock_pipeline.call_args
        assert call_args[1]["sequential"] is True
