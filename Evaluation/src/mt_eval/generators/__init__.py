"""Strategy registry and resolver for Dafny test generators.

STRATEGY_REGISTRY is auto-populated by @register_strategy decorator
on each subclass import.
"""

from src.mt_eval.generators.dafny_test_generator import (
    DafnyTestGenerator,
    STRATEGY_REGISTRY,
)

# Import subclasses to trigger @register_strategy
from src.mt_eval.generators.spec_test_generator import SpecTestGenerator  # noqa: F401
from src.mt_eval.generators.block_test_generator import BlockTestGenerator  # noqa: F401


def resolve_strategies(names: list[str]) -> list[DafnyTestGenerator]:
    """Instantiate strategies by name. Raises ValueError for unknown names."""
    unknown = [n for n in names if n not in STRATEGY_REGISTRY]
    if unknown:
        available = ", ".join(sorted(STRATEGY_REGISTRY.keys()))
        raise ValueError(
            f"Unknown strategy name(s): {unknown}. Available: {available}"
        )
    return [STRATEGY_REGISTRY[n]() for n in names]
