"""SpecBvaTestGenerator — Spec+BVA mode subclass of DafnyTestGenerator."""

from pathlib import Path

from src.mt_eval.generators.dafny_test_generator import DafnyTestGenerator, register_strategy
from src import config


@register_strategy("Spec_bva")
class SpecBvaTestGenerator(DafnyTestGenerator):
    """Spec-mode test generator with --bva flag."""

    def __init__(self, dafny_binary: Path | None = None, **kwargs):
        super().__init__(mode="Spec_bva", **kwargs)
        self.dafny_binary = dafny_binary or config.SPECTEST_DAFNY_BINARY

    def _build_cmd(self, dafny_file: Path) -> list[str]:
        return [
            str(self.dafny_binary),
            "generate-tests",
            "Spec",
            "--bva",
            str(dafny_file.resolve()),
            "--length-limit", "50",
            "--ignore-warnings",
        ]
