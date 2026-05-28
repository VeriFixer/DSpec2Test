"""SpecTestGenerator — Spec mode subclass of DafnyTestGenerator."""

from pathlib import Path

from src.mt_eval.generators.dafny_test_generator import DafnyTestGenerator, register_strategy
from src import config


@register_strategy("Spec")
class SpecTestGenerator(DafnyTestGenerator):
    """Spec-mode test generator. Builds its own command."""

    def __init__(self, dafny_binary: Path | None = None, **kwargs):
        super().__init__(mode="Spec", **kwargs)
        self.dafny_binary = dafny_binary or config.SPECTEST_DAFNY_BINARY

    def _build_cmd(self, dafny_file: Path) -> list[str]:
        return [
            str(self.dafny_binary),
            "generate-tests",
            "Spec",
            str(dafny_file.resolve()),
            "--repeat", "7",
            "--length-limit", "50",
            "--ignore-warnings",
            f"--solver-option:O:memory_max_size={config.DAFNY_MAX_MEMORY_MB}",
        ]
