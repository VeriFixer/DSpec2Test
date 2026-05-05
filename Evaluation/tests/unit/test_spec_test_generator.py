"""Unit tests for SpecTestGenerator."""

import subprocess
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

from src.mt_eval.generators.spec_test_generator import SpecTestGenerator
from src.mt_eval.core.abstract import TestGenResult


@pytest.fixture
def generator(tmp_path):
    """Generator with a fake binary path."""
    return SpecTestGenerator(dafny_binary=tmp_path / "dafny")


class TestSpecTestGeneratorInit:
    def test_name(self, generator):
        assert generator.name == "SpecTestGenerator"

    def test_custom_binary(self, tmp_path):
        binary = tmp_path / "my_dafny"
        gen = SpecTestGenerator(dafny_binary=binary)
        assert gen.dafny_binary == binary

    def test_default_binary(self):
        from src import config

        gen = SpecTestGenerator()
        assert gen.dafny_binary == config.DAFNY_BINARY


class TestGenerateTestsSuccess:
    @patch("src.mt_eval.generators.spec_test_generator.subprocess.run")
    def test_success_returns_result(self, mock_run, tmp_path):
        output_file = tmp_path / "out.dfy"
        output_file.write_text("// tests")
        dafny_file = tmp_path / "input.dfy"
        dafny_file.write_text("// source")

        mock_run.return_value = MagicMock(returncode=0, stderr="", stdout="method {:test} T() {}\n")

        gen = SpecTestGenerator(dafny_binary=Path("/usr/bin/dafny"))
        result = gen.generate_tests(dafny_file, output_file)

        assert result.success is True
        assert result.test_file == output_file
        assert result.error_message == ""
        assert result.command != ""

    @patch("src.mt_eval.generators.spec_test_generator.subprocess.run")
    def test_success_but_no_output_file(self, mock_run, tmp_path):
        output_file = tmp_path / "out.dfy"  # does not exist
        dafny_file = tmp_path / "input.dfy"
        dafny_file.write_text("// source")

        mock_run.return_value = MagicMock(returncode=0, stderr="", stdout="")

        gen = SpecTestGenerator(dafny_binary=Path("/usr/bin/dafny"))
        result = gen.generate_tests(dafny_file, output_file)

        assert result.success is False
        assert result.test_file is None


class TestGenerateTestsFailure:
    @patch("src.mt_eval.generators.spec_test_generator.subprocess.run")
    def test_nonzero_exit(self, mock_run, tmp_path):
        dafny_file = tmp_path / "input.dfy"
        output_file = tmp_path / "out.dfy"

        mock_run.return_value = MagicMock(returncode=1, stderr="some error")

        gen = SpecTestGenerator(dafny_binary=Path("/usr/bin/dafny"))
        result = gen.generate_tests(dafny_file, output_file)

        assert result.success is False
        assert result.test_file is None
        assert "some error" in result.error_message

    @patch("src.mt_eval.generators.spec_test_generator.subprocess.run")
    def test_timeout(self, mock_run, tmp_path):
        dafny_file = tmp_path / "input.dfy"
        output_file = tmp_path / "out.dfy"

        mock_run.side_effect = subprocess.TimeoutExpired(cmd="dafny", timeout=300)

        gen = SpecTestGenerator(dafny_binary=Path("/usr/bin/dafny"))
        result = gen.generate_tests(dafny_file, output_file)

        assert result.success is False
        assert result.test_file is None
        assert result.error_message == "timeout"

    @patch("src.mt_eval.generators.spec_test_generator.subprocess.run")
    def test_other_exception(self, mock_run, tmp_path):
        dafny_file = tmp_path / "input.dfy"
        output_file = tmp_path / "out.dfy"

        mock_run.side_effect = OSError("No such file or directory")

        gen = SpecTestGenerator(dafny_binary=Path("/usr/bin/dafny"))
        result = gen.generate_tests(dafny_file, output_file)

        assert result.success is False
        assert result.test_file is None
        assert "No such file or directory" in result.error_message


class TestSubprocessCommand:
    @patch("src.mt_eval.generators.spec_test_generator.subprocess.run")
    def test_correct_command(self, mock_run, tmp_path):
        dafny_file = tmp_path / "input.dfy"
        output_file = tmp_path / "out.dfy"
        output_file.write_text("// tests")

        mock_run.return_value = MagicMock(returncode=0, stderr="", stdout="method {:test} T() {}\n")

        binary = Path("/opt/dafny/dafny")
        gen = SpecTestGenerator(dafny_binary=binary)
        gen.generate_tests(dafny_file, output_file)

        mock_run.assert_called_once()
        cmd = mock_run.call_args[0][0]
        assert cmd == [
            str(binary),
            "generate-tests",
            "Spec",
            str(dafny_file.resolve()),
            "--test-count",
            "1",
            "--length-limit",
            "50",
            "--ignore-warnings",
        ]

    @patch("src.mt_eval.generators.spec_test_generator.subprocess.run")
    def test_uses_testgen_timeout(self, mock_run, tmp_path):
        from src import config

        dafny_file = tmp_path / "input.dfy"
        output_file = tmp_path / "out.dfy"
        output_file.write_text("// tests")

        mock_run.return_value = MagicMock(returncode=0, stderr="")

        gen = SpecTestGenerator(dafny_binary=Path("/usr/bin/dafny"))
        gen.generate_tests(dafny_file, output_file)

        kwargs = mock_run.call_args[1]
        assert kwargs["timeout"] == config.TESTGEN_TIMEOUT
