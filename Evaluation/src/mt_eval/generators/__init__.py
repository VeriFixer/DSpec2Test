"""Strategy registry and resolver for Dafny test generators.

STRATEGY_REGISTRY is auto-populated by @register_strategy decorator
on each subclass import. Subclasses are auto-discovered from this package.
"""

import importlib
import pkgutil
from pathlib import Path

from src.mt_eval.generators.dafny_test_generator import (
    DafnyTestGenerator,
    STRATEGY_REGISTRY,
)

# Auto-discover and import all modules in this package to trigger @register_strategy
_pkg_dir = Path(__file__).resolve().parent
for _finder, _name, _ispkg in pkgutil.iter_modules([str(_pkg_dir)]):
    if _name != "dafny_test_generator":
        importlib.import_module(f"{__name__}.{_name}")


def resolve_strategies(names: list[str]) -> list[DafnyTestGenerator]:
    """Instantiate strategies by name. Raises ValueError for unknown names."""
    unknown = [n for n in names if n not in STRATEGY_REGISTRY]
    if unknown:
        available = ", ".join(sorted(STRATEGY_REGISTRY.keys()))
        raise ValueError(
            f"Unknown strategy name(s): {unknown}. Available: {available}"
        )
    return [STRATEGY_REGISTRY[n]() for n in names]
