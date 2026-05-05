"""Unit tests for src.mt_eval.reporting.summary."""

import json

from src.mt_eval.core.models import MutantResult, MutantStatus
from src.mt_eval.metrics.kill_rate import KillRateMetrics, compute_kill_rate
from src.mt_eval.reporting.summary import print_summary, write_json_results


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _sample_results() -> list[MutantResult]:
    return [
        MutantResult("a__1-2_CBE.dfy", "a.dfy", MutantStatus.KILLED, 1.5),
        MutantResult("b__3-4_CBE.dfy", "b.dfy", MutantStatus.SURVIVED, 2.0),
        MutantResult("c__5-6_CBE.dfy", "c.dfy", MutantStatus.TIMEOUT, 300.0),
        MutantResult("d__7-8_CBE.dfy", "d.dfy", MutantStatus.KILLED, 0.8),
    ]


def _sample_metrics() -> KillRateMetrics:
    return compute_kill_rate(_sample_results())


# ---------------------------------------------------------------------------
# print_summary
# ---------------------------------------------------------------------------

class TestPrintSummary:
    def test_prints_header_and_row(self, capsys):
        metrics = _sample_metrics()
        print_summary(metrics)
        out = capsys.readouterr().out

        assert "Total" in out
        assert "Killed" in out
        assert "Survived" in out
        assert "Timeout" in out
        assert "Kill Rate" in out
        # row values
        assert "4" in out   # total
        assert "2" in out   # killed
        assert "1" in out   # survived

    def test_zero_results(self, capsys):
        metrics = KillRateMetrics(0, 0, 0, 0, 0, 0.0)
        print_summary(metrics)
        out = capsys.readouterr().out
        assert "0" in out

    def test_kill_rate_formatting(self, capsys):
        metrics = KillRateMetrics(10, 8, 2, 0, 0, 0.8)
        print_summary(metrics)
        out = capsys.readouterr().out
        assert "80.0%" in out


# ---------------------------------------------------------------------------
# write_json_results
# ---------------------------------------------------------------------------

class TestWriteJsonResults:
    def test_creates_file(self, tmp_path):
        results = _sample_results()
        metrics = _sample_metrics()
        out = tmp_path / "results.json"

        write_json_results(results, metrics, out)
        assert out.exists()

    def test_json_structure(self, tmp_path):
        results = _sample_results()
        metrics = _sample_metrics()
        out = tmp_path / "results.json"

        write_json_results(
            results, metrics, out,
            dataset_name="test_ds", generator_name="TestGen",
        )
        data = json.loads(out.read_text())

        assert "metadata" in data
        assert "summary" in data
        assert "results" in data

    def test_metadata_fields(self, tmp_path):
        results = _sample_results()
        metrics = _sample_metrics()
        out = tmp_path / "results.json"

        write_json_results(
            results, metrics, out,
            dataset_name="sample_100", generator_name="SpecTestGenerator",
        )
        meta = json.loads(out.read_text())["metadata"]

        assert meta["dataset"] == "sample_100"
        assert meta["generator"] == "SpecTestGenerator"
        assert meta["total_mutants"] == 4
        assert "timestamp" in meta

    def test_summary_matches_metrics(self, tmp_path):
        results = _sample_results()
        metrics = _sample_metrics()
        out = tmp_path / "results.json"

        write_json_results(results, metrics, out)
        summary = json.loads(out.read_text())["summary"]

        assert summary["killed"] == metrics.killed
        assert summary["survived"] == metrics.survived
        assert summary["timeout"] == metrics.timeout
        assert summary["kill_rate"] == metrics.kill_rate

    def test_per_mutant_entries(self, tmp_path):
        results = _sample_results()
        metrics = _sample_metrics()
        out = tmp_path / "results.json"

        write_json_results(results, metrics, out)
        entries = json.loads(out.read_text())["results"]

        assert len(entries) == len(results)
        first = entries[0]
        assert first["mutant_name"] == "a__1-2_CBE.dfy"
        assert first["original_name"] == "a.dfy"
        assert first["status"] == "killed"
        assert first["execution_time"] == 1.5

    def test_creates_parent_dirs(self, tmp_path):
        out = tmp_path / "nested" / "deep" / "results.json"
        write_json_results([], KillRateMetrics(0, 0, 0, 0, 0, 0.0), out)
        assert out.exists()

    def test_empty_results(self, tmp_path):
        out = tmp_path / "results.json"
        metrics = KillRateMetrics(0, 0, 0, 0, 0, 0.0)
        write_json_results([], metrics, out)

        data = json.loads(out.read_text())
        assert data["results"] == []
        assert data["summary"]["killed"] == 0

    def test_default_metadata_names(self, tmp_path):
        out = tmp_path / "results.json"
        write_json_results([], KillRateMetrics(0, 0, 0, 0, 0, 0.0), out)
        meta = json.loads(out.read_text())["metadata"]
        assert meta["dataset"] == "unknown"
        assert meta["generator"] == "unknown"
