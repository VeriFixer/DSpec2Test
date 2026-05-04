"""Integration tests for mutation pipeline — no mocks, real binaries.

These tests invoke the actual Dafny binary + MutDafny plugin.
They require:
  - Dafny binary at config.DAFNY_BINARY
  - MutDafny plugin built at config.MUTDAFNY_PLUGIN
  - DafnyBench ground_truth files present

Run with: pytest tests/integration/ -v
Skip if environment not ready: tests auto-skip via markers.
"""

import subprocess
from pathlib import Path

import pytest

from src.config import DAFNY_BINARY, MUTDAFNY_PLUGIN, EXTERNAL_ROOT, MUTDAFNY_DAFNY_BINARY
from src.mt_eval.core.mutation import apply_mutation, generate_diff
from src.mt_eval.core.verification import verify_program

# --- Fixtures & Markers ---

GROUND_TRUTH_DIR = EXTERNAL_ROOT / "bench" / "dafnybench" / "DafnyBench" / "dataset" / "ground_truth"
SAMPLE_FILE = GROUND_TRUTH_DIR / "Clover_abs.dfy"


def _dafny_available() -> bool:
    """Check if Dafny binary exists and is executable."""
    try:
        result = subprocess.run(
            [str(DAFNY_BINARY), "--version"],
            capture_output=True, timeout=30
        )
        return result.returncode == 0
    except (OSError, subprocess.TimeoutExpired):
        return False


def _mutdafny_available() -> bool:
    """Check if MutDafny plugin DLL and its bundled Dafny exist."""
    return MUTDAFNY_PLUGIN.exists() and MUTDAFNY_DAFNY_BINARY.exists()


def _sample_file_available() -> bool:
    """Check if sample .dfy file exists."""
    return SAMPLE_FILE.exists()


skip_no_dafny = pytest.mark.skipif(
    not _dafny_available(),
    reason=f"Dafny binary not available at {DAFNY_BINARY}"
)
skip_no_mutdafny = pytest.mark.skipif(
    not _mutdafny_available(),
    reason=f"MutDafny plugin not built at {MUTDAFNY_PLUGIN}"
)
skip_no_sample = pytest.mark.skipif(
    not _sample_file_available(),
    reason=f"Sample file not found: {SAMPLE_FILE}"
)


# --- Tests ---

@skip_no_dafny
class TestDafnyBinaryWorks:
    """Verify the Dafny binary itself is functional."""

    def test_dafny_version(self):
        """Dafny --version returns 0."""
        result = subprocess.run(
            [str(DAFNY_BINARY), "--version"],
            capture_output=True, text=True, timeout=30
        )
        assert result.returncode == 0
        # Output is version string like "4.11.0+hash"
        assert len(result.stdout.strip()) > 0

    @skip_no_sample
    def test_dafny_verify_valid_file(self):
        """Dafny can verify a known-good file."""
        result = subprocess.run(
            [str(DAFNY_BINARY), "verify", "--allow-warnings", str(SAMPLE_FILE)],
            capture_output=True, text=True, timeout=120
        )
        # Should verify successfully (0 errors)
        assert result.returncode == 0 or "0 errors" in result.stdout


@skip_no_dafny
@skip_no_mutdafny
@skip_no_sample
class TestMutDafnyScan:
    """Test the MutDafny scan pass (target discovery)."""

    def test_scan_produces_targets_csv(self, tmp_path):
        """Running scan on a valid file produces targets.csv."""
        result = subprocess.run(
            [
                str(MUTDAFNY_DAFNY_BINARY), "verify", str(SAMPLE_FILE),
                "--allow-warnings",
                f"--plugin:{MUTDAFNY_PLUGIN},scan",
            ],
            capture_output=True, text=True, timeout=120,
            cwd=str(tmp_path),
        )
        targets_file = tmp_path / "targets.csv"
        assert targets_file.exists(), (
            f"targets.csv not created. stdout={result.stdout[:500]}, "
            f"stderr={result.stderr[:500]}"
        )
        content = targets_file.read_text().strip()
        assert len(content) > 0, "targets.csv is empty"

    def test_scan_targets_have_valid_format(self, tmp_path):
        """Each line in targets.csv has at least 2 comma-separated fields."""
        subprocess.run(
            [
                str(MUTDAFNY_DAFNY_BINARY), "verify", str(SAMPLE_FILE),
                "--allow-warnings",
                f"--plugin:{MUTDAFNY_PLUGIN},scan",
            ],
            capture_output=True, timeout=120,
            cwd=str(tmp_path),
        )
        targets_file = tmp_path / "targets.csv"
        if not targets_file.exists():
            pytest.skip("targets.csv not produced")

        for line in targets_file.read_text().strip().splitlines():
            parts = line.split(",")
            assert len(parts) >= 2, f"Malformed target line: {line}"


@skip_no_dafny
@skip_no_mutdafny
@skip_no_sample
class TestMutDafnyMutate:
    """Test the full mutation pass (scan + mutate)."""

    def test_mutation_produces_dfy_file(self, tmp_path):
        """Full scan+mutate produces at least one .dfy mutant."""
        # Scan first
        subprocess.run(
            [
                str(MUTDAFNY_DAFNY_BINARY), "verify", str(SAMPLE_FILE),
                "--allow-warnings",
                f"--plugin:{MUTDAFNY_PLUGIN},scan",
            ],
            capture_output=True, timeout=120,
            cwd=str(tmp_path),
        )
        targets_file = tmp_path / "targets.csv"
        if not targets_file.exists():
            pytest.skip("Scan produced no targets")

        # Try first target
        lines = targets_file.read_text().strip().splitlines()
        if not lines:
            pytest.skip("targets.csv empty")

        parts = lines[0].split(",")
        pos = parts[0].strip()
        op = parts[1].strip() if len(parts) > 1 else ""
        arg = parts[2].strip() if len(parts) > 2 else ""

        plugin_arg = f"mut {pos} {op}" + (f" {arg}" if arg else "")

        subprocess.run(
            [
                str(MUTDAFNY_DAFNY_BINARY), "verify", str(SAMPLE_FILE),
                "--allow-warnings",
                f"--plugin:{MUTDAFNY_PLUGIN},{plugin_arg}",
            ],
            capture_output=True, timeout=120,
            cwd=str(tmp_path),
        )

        mutants = list(tmp_path.glob("*.dfy"))
        assert len(mutants) > 0, "No .dfy mutant files produced"

    def test_mutant_differs_from_original(self, tmp_path):
        """Produced mutant should differ from original."""
        # Scan
        subprocess.run(
            [
                str(MUTDAFNY_DAFNY_BINARY), "verify", str(SAMPLE_FILE),
                "--allow-warnings",
                f"--plugin:{MUTDAFNY_PLUGIN},scan",
            ],
            capture_output=True, timeout=120,
            cwd=str(tmp_path),
        )
        targets_file = tmp_path / "targets.csv"
        if not targets_file.exists():
            pytest.skip("Scan produced no targets")

        lines = targets_file.read_text().strip().splitlines()
        if not lines:
            pytest.skip("targets.csv empty")

        parts = lines[0].split(",")
        pos = parts[0].strip()
        op = parts[1].strip() if len(parts) > 1 else ""
        arg = parts[2].strip() if len(parts) > 2 else ""
        plugin_arg = f"mut {pos} {op}" + (f" {arg}" if arg else "")

        subprocess.run(
            [
                str(MUTDAFNY_DAFNY_BINARY), "verify", str(SAMPLE_FILE),
                "--allow-warnings",
                f"--plugin:{MUTDAFNY_PLUGIN},{plugin_arg}",
            ],
            capture_output=True, timeout=120,
            cwd=str(tmp_path),
        )

        mutants = list(tmp_path.glob("*.dfy"))
        if not mutants:
            pytest.skip("No mutant produced")

        original_text = SAMPLE_FILE.read_text()
        mutant_text = mutants[0].read_text()
        assert mutant_text != original_text, "Mutant is identical to original"


@skip_no_dafny
@skip_no_mutdafny
@skip_no_sample
class TestApplyMutationIntegration:
    """Test the apply_mutation Python function end-to-end."""

    def test_apply_mutation_returns_path(self, tmp_path):
        """apply_mutation returns a valid Path to a .dfy mutant."""
        out_dir = tmp_path / "mutants"
        result = apply_mutation(SAMPLE_FILE, out_dir)

        if result is None:
            pytest.skip("MutDafny produced no mutants for this file (may be expected)")

        assert result.exists()
        assert result.suffix == ".dfy"
        assert result.parent == out_dir

    def test_apply_mutation_mutant_content_differs(self, tmp_path):
        """Mutant file content differs from original."""
        out_dir = tmp_path / "mutants"
        result = apply_mutation(SAMPLE_FILE, out_dir)

        if result is None:
            pytest.skip("No mutant produced")

        assert result.read_text() != SAMPLE_FILE.read_text()

    def test_generate_diff_on_real_mutant(self, tmp_path):
        """generate_diff produces non-empty diff for real mutant."""
        out_dir = tmp_path / "mutants"
        mutant = apply_mutation(SAMPLE_FILE, out_dir)

        if mutant is None:
            pytest.skip("No mutant produced")

        diff_path = tmp_path / "diff.patch"
        generate_diff(SAMPLE_FILE, mutant, diff_path)

        assert diff_path.exists()
        content = diff_path.read_text()
        assert len(content) > 0, "Diff is empty for a mutant that should differ"
        assert "---" in content
        assert "+++" in content


@skip_no_dafny
@skip_no_sample
class TestVerificationIntegration:
    """Test verification of Dafny files."""

    def test_verify_valid_file_passes(self):
        """A known-good file should pass verification."""
        passed = verify_program(SAMPLE_FILE)
        assert passed is True

    def test_verify_invalid_file_fails(self, tmp_path):
        """A file with broken postcondition should fail verification."""
        bad_file = tmp_path / "bad.dfy"
        bad_file.write_text(
            "method Bad(x: int) returns (y: int)\n"
            "  ensures y > x\n"  # impossible for all x
            "{\n"
            "  return x;\n"
            "}\n"
        )
        passed = verify_program(bad_file)
        assert passed is False
