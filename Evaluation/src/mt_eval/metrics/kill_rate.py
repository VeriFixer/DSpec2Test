"""Kill rate computation for mutation testing results."""

from dataclasses import dataclass

from src.mt_eval.core.models import MutantResult, MutantStatus


@dataclass
class KillRateMetrics:
    """Aggregated kill rate metrics.

    Attributes:
        total: Total number of mutants evaluated.
        killed: Count with status KILLED.
        survived: Count with status SURVIVED.
        timeout: Count with status TIMEOUT.
        error: Count with status ERROR.
        kill_rate: killed / (total - timeout - error), 0.0 if denominator is zero.
    """

    total: int
    killed: int
    survived: int
    timeout: int
    error: int
    kill_rate: float


def compute_kill_rate(results: list[MutantResult]) -> KillRateMetrics:
    """Compute kill rate metrics from a list of mutant results.

    Kill rate formula: killed / (total - timeout - error).
    If the denominator is zero, kill_rate is 0.0.
    """
    total = len(results)
    killed = sum(1 for r in results if r.status == MutantStatus.KILLED)
    survived = sum(1 for r in results if r.status == MutantStatus.SURVIVED)
    timeout = sum(1 for r in results if r.status == MutantStatus.TIMEOUT)
    error = sum(1 for r in results if r.status == MutantStatus.ERROR)

    denominator = total - timeout - error
    kill_rate = killed / denominator if denominator > 0 else 0.0

    return KillRateMetrics(
        total=total,
        killed=killed,
        survived=survived,
        timeout=timeout,
        error=error,
        kill_rate=kill_rate,
    )
