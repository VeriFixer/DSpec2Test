"""Unit tests for kill rate computation."""

import pytest

from src.mt_eval.core.models import MutantResult, MutantStatus
from src.mt_eval.metrics.kill_rate import KillRateMetrics, compute_kill_rate


def _make_result(status: MutantStatus) -> MutantResult:
    return MutantResult(
        mutant_name="m.dfy",
        original_name="o.dfy",
        status=status,
        execution_time=1.0,
    )


class TestComputeKillRate:
    """Tests for compute_kill_rate."""

    def test_empty_results(self):
        metrics = compute_kill_rate([])
        assert metrics == KillRateMetrics(0, 0, 0, 0, 0, 0.0)

    def test_all_killed(self):
        results = [_make_result(MutantStatus.KILLED) for _ in range(5)]
        metrics = compute_kill_rate(results)
        assert metrics.total == 5
        assert metrics.killed == 5
        assert metrics.survived == 0
        assert metrics.kill_rate == 1.0

    def test_all_survived(self):
        results = [_make_result(MutantStatus.SURVIVED) for _ in range(3)]
        metrics = compute_kill_rate(results)
        assert metrics.total == 3
        assert metrics.killed == 0
        assert metrics.survived == 3
        assert metrics.kill_rate == 0.0

    def test_mixed_statuses(self):
        results = [
            _make_result(MutantStatus.KILLED),
            _make_result(MutantStatus.KILLED),
            _make_result(MutantStatus.SURVIVED),
            _make_result(MutantStatus.TIMEOUT),
            _make_result(MutantStatus.ERROR),
        ]
        metrics = compute_kill_rate(results)
        assert metrics.total == 5
        assert metrics.killed == 2
        assert metrics.survived == 1
        assert metrics.timeout == 1
        assert metrics.error == 1
        # denominator = 5 - 1 - 1 = 3, kill_rate = 2/3
        assert metrics.kill_rate == pytest.approx(2.0 / 3.0)

    def test_all_timeout_and_error_gives_zero_rate(self):
        results = [
            _make_result(MutantStatus.TIMEOUT),
            _make_result(MutantStatus.ERROR),
        ]
        metrics = compute_kill_rate(results)
        assert metrics.total == 2
        assert metrics.kill_rate == 0.0

    def test_counts_match_input(self):
        results = [
            _make_result(MutantStatus.KILLED),
            _make_result(MutantStatus.SURVIVED),
            _make_result(MutantStatus.TIMEOUT),
            _make_result(MutantStatus.ERROR),
        ]
        metrics = compute_kill_rate(results)
        assert metrics.killed + metrics.survived + metrics.timeout + metrics.error == metrics.total
