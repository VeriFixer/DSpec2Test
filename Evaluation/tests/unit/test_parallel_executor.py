"""Unit tests for parallel_executor module."""
import pytest
from src.mt_eval.execution.parallel_executor import (
    run_parallel_or_seq,
    PHYSICAL_CORES,
    SAFE_THREADS,
    CPU_LIMITER,
    shutdown_parallel_executor,
    _get_shared_executor,
)


def _square(x):
    return x * x


def _add(x, y):
    return x + y


class TestConstants:
    def test_physical_cores_positive(self):
        assert PHYSICAL_CORES >= 1

    def test_safe_threads_positive(self):
        assert SAFE_THREADS >= 1

    def test_safe_threads_equals_physical_cores(self):
        assert SAFE_THREADS == max(1, PHYSICAL_CORES)


class TestRunParallelOrSeq:
    def test_sequential_returns_ordered_results(self):
        results = run_parallel_or_seq(range(5), _square, "test", parallel=False)
        assert results == [0, 1, 4, 9, 16]

    def test_parallel_returns_all_results(self):
        results = run_parallel_or_seq(range(5), _square, "test", parallel=True)
        assert sorted(results) == [0, 1, 4, 9, 16]

    def test_extra_args_passed(self):
        results = run_parallel_or_seq(range(3), _add, "test", 10, parallel=False)
        assert results == [10, 11, 12]

    def test_extra_args_parallel(self):
        results = run_parallel_or_seq(range(3), _add, "test", 10, parallel=True)
        assert sorted(results) == [10, 11, 12]

    def test_empty_items(self):
        results = run_parallel_or_seq([], _square, "test", parallel=True)
        assert results == []

    def test_empty_items_sequential(self):
        results = run_parallel_or_seq([], _square, "test", parallel=False)
        assert results == []

    def test_error_handling_parallel(self):
        """Errors are caught and skipped, not raised."""
        def fail_on_two(x):
            if x == 2:
                raise ValueError("boom")
            return x

        results = run_parallel_or_seq(range(4), fail_on_two, "test", parallel=True)
        assert sorted(results) == [0, 1, 3]

    def test_error_handling_sequential(self):
        def fail_on_two(x):
            if x == 2:
                raise ValueError("boom")
            return x

        results = run_parallel_or_seq(range(4), fail_on_two, "test", parallel=False)
        assert results == [0, 1, 3]


class TestShutdownAndRestart:
    def test_shutdown_and_restart(self):
        """Executor can be shut down and recreated."""
        shutdown_parallel_executor(wait=True)
        # After shutdown, _get_shared_executor should recreate
        executor = _get_shared_executor()
        assert executor is not None
        # Verify it still works
        results = run_parallel_or_seq([1, 2, 3], _square, "test", parallel=True)
        assert sorted(results) == [1, 4, 9]
