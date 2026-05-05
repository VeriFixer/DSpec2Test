"""Sampler: randomly select N distinct Dafny files from DafnyBench."""

import logging
import random
from pathlib import Path

logger = logging.getLogger(__name__)

DEFAULT_SEED: int = 42


def sample_programs(dafnybench_dir: Path, n: int, seed: int = DEFAULT_SEED) -> list[Path]:
    """Randomly sample N distinct .dfy files from DafnyBench ground_truth dir.

    Globs recursively for *.dfy under dafnybench_dir/ground_truth/.
    If pool size < n, logs warning and returns all available files.

    Uses a fixed seed by default for reproducibility.

    Args:
        dafnybench_dir: Root of the DafnyBench repository.
        n: Number of programs to sample.
        seed: RNG seed for reproducibility. Default 42.

    Returns:
        List of Path objects to selected .dfy files.
    """
    ground_truth = dafnybench_dir / "DafnyBench" / "dataset" / "ground_truth"
    pool = sorted(ground_truth.rglob("*.dfy"))

    if len(pool) == 0:
        logger.warning("No .dfy files found in %s", ground_truth)
        return []

    if len(pool) < n:
        logger.warning(
            "Pool size (%d) < requested sample size (%d); returning all available",
            len(pool),
            n,
        )
        return pool

    rng = random.Random(seed)
    logger.info("Sampling %d programs with seed=%d", n, seed)
    return rng.sample(pool, n)
