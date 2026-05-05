"""Tests for TestGenerator ABC and TestGenResult dataclass."""

from pathlib import Path

import pytest

from src.mt_eval.core.abstract import TestGenResult, TestGenerator


class DummyGenerator(TestGenerator):
    """Concrete impl for testing."""

    def generate_tests(self, dafny_file: Path, output_file: Path) -> TestGenResult:
        return TestGenResult(success=True, test_file=output_file)


class TestTestGenResult:
    def test_success_result(self):
        r = TestGenResult(success=True, test_file=Path("/tmp/out.dfy"))
        assert r.success is True
        assert r.test_file == Path("/tmp/out.dfy")
        assert r.error_message == ""

    def test_failure_result(self):
        r = TestGenResult(success=False, test_file=None, error_message="timeout")
        assert r.success is False
        assert r.test_file is None
        assert r.error_message == "timeout"

    def test_default_error_message(self):
        r = TestGenResult(success=True, test_file=None)
        assert r.error_message == ""


class TestTestGenerator:
    def test_name_stored(self):
        gen = DummyGenerator(name="test-gen")
        assert gen.name == "test-gen"

    def test_kwargs_accepted(self):
        gen = DummyGenerator(name="test-gen", extra="ignored")
        assert gen.name == "test-gen"

    def test_generate_tests_returns_result(self, tmp_path):
        gen = DummyGenerator(name="dummy")
        out = tmp_path / "out.dfy"
        result = gen.generate_tests(Path("input.dfy"), out)
        assert isinstance(result, TestGenResult)
        assert result.success is True
        assert result.test_file == out

    def test_cannot_instantiate_abc(self):
        with pytest.raises(TypeError):
            TestGenerator(name="nope")  # type: ignore[abstract]
