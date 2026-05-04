"""Unit tests for src.runners.run_evaluation module."""

from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

from src.runners.run_evaluation import parse_args, run_pipeline, main, _validate_dataset, _derive_original_stem
from src.mt_eval.core.abstract import TestGenResult
from src.mt_eval.core.models import MutantResult, MutantStatus


# ---------------------------------------------------------------------------
# parse_args
# ---------------------------------------------------------------------------

class TestParseArgs:
    def test_positional_dataset_path(self):
        args = parse_args(["/data/my_dataset"])
        assert args.dataset_path == "/data/my_dataset"

    def test_defaults(self):
        args = parse_args(["ds"])
        assert args.clean_cache is False
        assert args.sequential is False
        assert args.output_dir is None

    def test_clean_cache(self):
        args = parse_args(["ds", "--clean-cache"])
        assert args.clean_cache is True

    def test_sequential(self):
        args = parse_args(["ds", "--sequential"])
        assert args.sequential is True

    def test_output_dir(self):
        args = parse_args(["ds", "--output-dir", "/tmp/out"])
        assert args.output_dir == "/tmp/out"

    def test_all_flags(self):
        args = parse_args(["ds", "--clean-cache", "--sequential", "--output-dir", "out"])
        assert args.clean_cache is True
        assert args.sequential is True
        assert args.output_dir == "out"

    def test_missing_dataset_path_exits(self):
        with pytest.raises(SystemExit):
            parse_args([])


# ---------------------------------------------------------------------------
# _validate_dataset
# ---------------------------------------------------------------------------

class TestValidateDataset:
    def test_valid_dataset(self, tmp_path):
        (tmp_path / "original").mkdir()
        (tmp_path / "killed").mkdir()
        assert _validate_dataset(tmp_path) is True

    def test_missing_original(self, tmp_path):
        (tmp_path / "killed").mkdir()
        assert _validate_dataset(tmp_path) is False

    def test_missing_killed(self, tmp_path):
        (tmp_path / "original").mkdir()
        assert _validate_dataset(tmp_path) is False

    def test_both_missing(self, tmp_path):
        assert _validate_dataset(tmp_path) is False


# ---------------------------------------------------------------------------
# _derive_original_stem
# ---------------------------------------------------------------------------

class TestDeriveOriginalStem:
    def test_standard_mutant_name(self):
        assert _derive_original_stem("abs__161-188_CBE.dfy") == "abs"

    def test_no_double_underscore(self):
        assert _derive_original_stem("simple.dfy") == "simple"

    def test_complex_stem(self):
        assert _derive_original_stem("my_prog__10-20_XYZ.dfy") == "my_prog"


# ---------------------------------------------------------------------------
# run_pipeline
# ---------------------------------------------------------------------------

def _make_dataset(tmp_path, originals=None, mutants=None):
    """Helper: create dataset dir with original/ and killed/ containing .dfy files."""
    ds = tmp_path / "dataset"
    orig_dir = ds / "original"
    kill_dir = ds / "killed"
    orig_dir.mkdir(parents=True)
    kill_dir.mkdir(parents=True)

    originals = originals or ["prog.dfy"]
    mutants = mutants or ["prog__1-2_CBE.dfy"]

    for name in originals:
        (orig_dir / name).write_text(f"// {name}")
    for name in mutants:
        (kill_dir / name).write_text(f"// {name}")

    return ds


class TestRunPipeline:
    def test_nonexistent_dataset_returns_1(self, tmp_path):
        result = run_pipeline(
            tmp_path / "nope",
            clean_cache=False, sequential=False, output_dir=tmp_path,
        )
        assert result == 1

    def test_missing_subdirs_returns_1(self, tmp_path):
        tmp_path.mkdir(exist_ok=True)
        result = run_pipeline(
            tmp_path,
            clean_cache=False, sequential=False, output_dir=tmp_path,
        )
        assert result == 1

    @patch("src.runners.run_evaluation.SpecTestGenerator")
    def test_no_originals_returns_1(self, mock_gen_cls, tmp_path):
        """Empty original/ dir → failure."""
        ds = tmp_path / "ds"
        (ds / "original").mkdir(parents=True)
        (ds / "killed").mkdir(parents=True)

        result = run_pipeline(ds, clean_cache=False, sequential=False, output_dir=tmp_path)
        assert result == 1

    @patch("src.runners.run_evaluation.run_parallel_or_seq")
    @patch("src.runners.run_evaluation.SpecTestGenerator")
    def test_all_test_gen_fails_returns_1(self, mock_gen_cls, mock_par, tmp_path):
        """All test generation fails → critical failure."""
        ds = _make_dataset(tmp_path)

        mock_gen = MagicMock()
        mock_gen.name = "SpecTestGenerator"
        mock_gen.generate_tests.return_value = TestGenResult(
            success=False, test_file=None, error_message="timeout"
        )
        mock_gen_cls.return_value = mock_gen

        result = run_pipeline(ds, clean_cache=False, sequential=False, output_dir=tmp_path)
        assert result == 1
        mock_par.assert_not_called()

    @patch("src.runners.run_evaluation.run_parallel_or_seq")
    @patch("src.runners.run_evaluation.SpecTestGenerator")
    def test_no_matching_mutants_returns_1(self, mock_gen_cls, mock_par, tmp_path):
        """Tests generated but no mutant matches → failure."""
        ds = _make_dataset(tmp_path, originals=["a.dfy"], mutants=["b__1-2_X.dfy"])

        test_file = ds / "tests" / "a.test.dfy"
        test_file.parent.mkdir(parents=True, exist_ok=True)
        test_file.write_text("// test")

        mock_gen = MagicMock()
        mock_gen.name = "SpecTestGenerator"
        mock_gen.generate_tests.return_value = TestGenResult(
            success=True, test_file=test_file
        )
        mock_gen_cls.return_value = mock_gen

        result = run_pipeline(ds, clean_cache=False, sequential=False, output_dir=tmp_path)
        assert result == 1

    @patch("src.runners.run_evaluation.write_json_results")
    @patch("src.runners.run_evaluation.print_summary")
    @patch("src.runners.run_evaluation.run_parallel_or_seq")
    @patch("src.runners.run_evaluation.SpecTestGenerator")
    def test_success_pipeline(self, mock_gen_cls, mock_par, mock_print, mock_write, tmp_path):
        """Full success: test gen → kill check → metrics → report."""
        ds = _make_dataset(tmp_path)

        test_file = ds / "tests" / "prog.test.dfy"
        test_file.parent.mkdir(parents=True, exist_ok=True)
        test_file.write_text("// test")

        mock_gen = MagicMock()
        mock_gen.name = "SpecTestGenerator"
        mock_gen.generate_tests.return_value = TestGenResult(
            success=True, test_file=test_file
        )
        mock_gen_cls.return_value = mock_gen

        killed_result = MutantResult(
            mutant_name="prog__1-2_CBE.dfy",
            original_name="prog.dfy",
            status=MutantStatus.KILLED,
            execution_time=1.5,
        )
        mock_par.return_value = [killed_result]

        result = run_pipeline(ds, clean_cache=False, sequential=False, output_dir=tmp_path)
        assert result == 0
        mock_print.assert_called_once()
        mock_write.assert_called_once()

    @patch("src.runners.run_evaluation.write_json_results")
    @patch("src.runners.run_evaluation.print_summary")
    @patch("src.runners.run_evaluation.run_parallel_or_seq")
    @patch("src.runners.run_evaluation.SpecTestGenerator")
    def test_sequential_prints_debug(self, mock_gen_cls, mock_par, mock_print, mock_write, tmp_path, capsys):
        """Sequential mode prints per-mutant debug info."""
        ds = _make_dataset(tmp_path)

        test_file = ds / "tests" / "prog.test.dfy"
        test_file.parent.mkdir(parents=True, exist_ok=True)
        test_file.write_text("// test")

        mock_gen = MagicMock()
        mock_gen.name = "SpecTestGenerator"
        mock_gen.generate_tests.return_value = TestGenResult(
            success=True, test_file=test_file
        )
        mock_gen_cls.return_value = mock_gen

        killed_result = MutantResult(
            mutant_name="prog__1-2_CBE.dfy",
            original_name="prog.dfy",
            status=MutantStatus.KILLED,
            execution_time=2.0,
        )
        mock_par.return_value = [killed_result]

        run_pipeline(ds, clean_cache=False, sequential=True, output_dir=tmp_path)

        captured = capsys.readouterr()
        assert "[run_evaluation]" in captured.out
        assert "prog__1-2_CBE.dfy" in captured.out
        assert "killed" in captured.out

    @patch("src.runners.run_evaluation.SpecTestGenerator")
    def test_clean_cache_removes_tests_dir(self, mock_gen_cls, tmp_path):
        """--clean-cache removes tests/ subdir."""
        ds = _make_dataset(tmp_path)
        tests_dir = ds / "tests"
        tests_dir.mkdir()
        (tests_dir / "old.test.dfy").write_text("// old")

        mock_gen = MagicMock()
        mock_gen.name = "SpecTestGenerator"
        mock_gen.generate_tests.return_value = TestGenResult(
            success=False, test_file=None, error_message="fail"
        )
        mock_gen_cls.return_value = mock_gen

        # Will return 1 (all test gen fails) but cache should be cleaned
        run_pipeline(ds, clean_cache=True, sequential=False, output_dir=tmp_path)

        # Old file should be gone (dir recreated empty)
        assert not (tests_dir / "old.test.dfy").exists()

    @patch("src.runners.run_evaluation.write_json_results")
    @patch("src.runners.run_evaluation.print_summary")
    @patch("src.runners.run_evaluation.run_parallel_or_seq")
    @patch("src.runners.run_evaluation.SpecTestGenerator")
    def test_skips_mutants_without_tests(self, mock_gen_cls, mock_par, mock_print, mock_write, tmp_path):
        """Mutants whose original has no test are skipped."""
        ds = _make_dataset(
            tmp_path,
            originals=["a.dfy", "b.dfy"],
            mutants=["a__1-2_X.dfy", "b__3-4_Y.dfy"],
        )

        test_a = ds / "tests" / "a.test.dfy"
        test_a.parent.mkdir(parents=True, exist_ok=True)
        test_a.write_text("// test a")

        mock_gen = MagicMock()
        mock_gen.name = "SpecTestGenerator"

        def gen_side_effect(dfy_file, output_file):
            if dfy_file.stem == "a":
                return TestGenResult(success=True, test_file=test_a)
            return TestGenResult(success=False, test_file=None, error_message="fail")

        mock_gen.generate_tests.side_effect = gen_side_effect
        mock_gen_cls.return_value = mock_gen

        mock_par.return_value = [
            MutantResult("a__1-2_X.dfy", "a.dfy", MutantStatus.KILLED, 1.0)
        ]

        result = run_pipeline(ds, clean_cache=False, sequential=False, output_dir=tmp_path)
        assert result == 0

        # Only 1 task submitted (a's mutant), b's mutant skipped
        call_args = mock_par.call_args
        items = list(call_args[0][0])
        assert len(items) == 1

    @patch("src.runners.run_evaluation.write_json_results")
    @patch("src.runners.run_evaluation.print_summary")
    @patch("src.runners.run_evaluation.run_parallel_or_seq")
    @patch("src.runners.run_evaluation.SpecTestGenerator")
    def test_no_mutant_dfy_files_returns_1(self, mock_gen_cls, mock_par, mock_print, mock_write, tmp_path):
        """killed/ has no .dfy files → failure."""
        ds = tmp_path / "ds"
        (ds / "original").mkdir(parents=True)
        (ds / "killed").mkdir(parents=True)
        (ds / "original" / "prog.dfy").write_text("// orig")
        # killed/ has only a .txt diff, no .dfy
        (ds / "killed" / "prog__1-2_X.txt").write_text("diff")

        test_file = ds / "tests" / "prog.test.dfy"
        test_file.parent.mkdir(parents=True, exist_ok=True)
        test_file.write_text("// test")

        mock_gen = MagicMock()
        mock_gen.name = "SpecTestGenerator"
        mock_gen.generate_tests.return_value = TestGenResult(success=True, test_file=test_file)
        mock_gen_cls.return_value = mock_gen

        result = run_pipeline(ds, clean_cache=False, sequential=False, output_dir=tmp_path)
        assert result == 1


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------

class TestMain:
    @patch("src.runners.run_evaluation.run_pipeline")
    def test_main_calls_pipeline(self, mock_pipeline):
        mock_pipeline.return_value = 0
        with pytest.raises(SystemExit) as exc_info:
            main(["/data/ds"])
        assert exc_info.value.code == 0
        mock_pipeline.assert_called_once()

    @patch("src.runners.run_evaluation.run_pipeline")
    def test_main_exits_nonzero_on_failure(self, mock_pipeline):
        mock_pipeline.return_value = 1
        with pytest.raises(SystemExit) as exc_info:
            main(["/data/ds"])
        assert exc_info.value.code == 1

    @patch("src.runners.run_evaluation.run_pipeline")
    def test_main_output_dir_default_is_dataset_path(self, mock_pipeline):
        """Default output_dir = dataset_path."""
        mock_pipeline.return_value = 0
        with pytest.raises(SystemExit):
            main(["/data/ds"])
        call_kwargs = mock_pipeline.call_args[1]
        assert call_kwargs["output_dir"] == Path("/data/ds")

    @patch("src.runners.run_evaluation.run_pipeline")
    def test_main_output_dir_override(self, mock_pipeline):
        mock_pipeline.return_value = 0
        with pytest.raises(SystemExit):
            main(["/data/ds", "--output-dir", "/tmp/out"])
        call_kwargs = mock_pipeline.call_args[1]
        assert call_kwargs["output_dir"] == Path("/tmp/out")

    @patch("src.runners.run_evaluation.run_pipeline")
    def test_main_clean_cache_flag(self, mock_pipeline):
        mock_pipeline.return_value = 0
        with pytest.raises(SystemExit):
            main(["/data/ds", "--clean-cache"])
        call_kwargs = mock_pipeline.call_args[1]
        assert call_kwargs["clean_cache"] is True

    @patch("src.runners.run_evaluation.run_pipeline")
    def test_main_sequential_flag(self, mock_pipeline):
        mock_pipeline.return_value = 0
        with pytest.raises(SystemExit):
            main(["/data/ds", "--sequential"])
        call_kwargs = mock_pipeline.call_args[1]
        assert call_kwargs["sequential"] is True
