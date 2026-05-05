"""Property-based tests for run_evaluation pipeline — safety check gating logic.

Property 4: Safety check failure skips all associated mutants.
For any program that fails the safety check, none of its mutants SHALL be
subjected to kill checking, and all its mutants SHALL be counted as not-supported.

**Validates: Requirements 4.2, 4.3, 4.4**
"""

import json
from pathlib import Path
from unittest.mock import MagicMock, patch

from hypothesis import given, settings, assume
from hypothesis import strategies as st

from src.mt_eval.core.abstract import TestGenResult
from src.mt_eval.core.models import MutantResult, MutantStatus
from src.runners.run_evaluation import run_pipeline


# --- Strategies ---

# Generate a list of program entries: (stem, safety_pass, n_mutants)
program_entry = st.tuples(
    st.from_regex(r"[a-z]{2,8}", fullmatch=True),  # stem
    st.booleans(),  # safety check pass/fail
    st.integers(min_value=1, max_value=5),  # number of mutants
)


@st.composite
def program_set(draw):
    """Generate a set of programs with unique stems, safety outcomes, and mutant counts."""
    entries = draw(st.lists(program_entry, min_size=1, max_size=10))
    # Deduplicate stems
    seen = set()
    unique = []
    for stem, safe, n_mut in entries:
        if stem not in seen:
            seen.add(stem)
            unique.append((stem, safe, n_mut))
    assume(len(unique) >= 1)
    # Ensure at least one program fails safety (to test the property meaningfully)
    # But also allow all-pass scenarios to verify no false positives
    return unique


def _setup_filesystem(tmp_path, programs):
    """Create .dfy files and mutant files in tmp dirs matching pipeline expectations."""
    programs_dir = tmp_path / "selected_programs"
    mutants_dir = tmp_path / "selected_programs_mutants"
    mutants_with_tests_dir = tmp_path / "selected_programs_mutants_with_tests"
    programs_dir.mkdir(parents=True)
    mutants_dir.mkdir(parents=True)
    mutants_with_tests_dir.mkdir(parents=True)

    for stem, _safe, n_mutants in programs:
        # Create original .dfy
        (programs_dir / f"{stem}.dfy").write_text(f"// {stem}")
        # Create mutant .dfy files
        for i in range(n_mutants):
            (mutants_dir / f"{stem}__{i}-{i+1}_CBE.dfy").write_text(f"// mutant {i}")

    return programs_dir, mutants_dir, mutants_with_tests_dir


class TestSafetyCheckGating:
    """Property 4: Safety check failure skips all associated mutants."""

    @given(programs=program_set())
    @settings(max_examples=100)
    def test_failed_safety_check_skips_kill_check(self, programs, tmp_path_factory):
        """Mutants of programs that fail safety check are NEVER passed to check_kill.

        **Validates: Requirements 4.2, 4.3, 4.4**
        """
        tmp_path = tmp_path_factory.mktemp("eval")
        programs_dir, mutants_dir, mutants_with_tests_dir = _setup_filesystem(
            tmp_path, programs
        )

        # Build safety map: stem -> bool
        safety_map = {stem: safe for stem, safe, _ in programs}

        # Track which mutants get kill-checked
        kill_checked_mutants: list[str] = []

        def mock_safety_check(original: Path, test_file: Path, **kwargs) -> bool:
            return safety_map[original.stem]

        def mock_check_kill(test_file: Path, mutant_file: Path) -> MutantResult:
            kill_checked_mutants.append(mutant_file.name)
            return MutantResult(
                mutant_name=mutant_file.name,
                original_name=f"{mutant_file.stem.split('__')[0]}.dfy",
                status=MutantStatus.KILLED,
                execution_time=0.1,
            )

        # Mock SpecTestGenerator to always succeed
        mock_gen_instance = MagicMock()
        mock_gen_instance.name = "DafnyTestGenerator_Spec"

        def mock_generate_tests(dfy_file: Path, output_file: Path) -> TestGenResult:
            output_file.parent.mkdir(parents=True, exist_ok=True)
            output_file.write_text(f"// tests for {dfy_file.stem}")
            return TestGenResult(success=True, test_file=output_file)

        mock_gen_instance.generate_tests.side_effect = mock_generate_tests

        # Patch config paths and dependencies
        with (
            patch("src.runners.run_evaluation.SELECTED_PROGRAMS_DIR", programs_dir),
            patch("src.runners.run_evaluation.SELECTED_PROGRAMS_MUTANTS_DIR", mutants_dir),
            patch(
                "src.runners.run_evaluation.SELECTED_PROGRAMS_MUTANTS_WITH_TESTS_DIR",
                mutants_with_tests_dir,
            ),
            patch("src.runners.run_evaluation.run_safety_check", side_effect=mock_safety_check),
            patch("src.runners.run_evaluation.SpecTestGenerator", return_value=mock_gen_instance),
            patch("src.runners.run_evaluation.KillChecker") as mock_checker_cls,
        ):
            mock_checker = MagicMock()
            mock_checker.check_kill.side_effect = mock_check_kill
            mock_checker_cls.return_value = mock_checker

            output_dir = tmp_path / "results"
            run_pipeline(sequential=True, output_dir=output_dir)

        # --- Assert Property 4 ---
        # Identify stems that failed safety
        failed_stems = {stem for stem, safe, _ in programs if not safe}

        # 1) No mutant of a failed program was kill-checked
        for mutant_name in kill_checked_mutants:
            mutant_stem = mutant_name.split("__")[0]
            assert mutant_stem not in failed_stems, (
                f"Mutant '{mutant_name}' was kill-checked but its program "
                f"'{mutant_stem}' failed safety check"
            )

        # 2) All mutants of failed programs are counted as not_supported in output
        results_file = output_dir / "results.json"
        if results_file.exists():
            data = json.loads(results_file.read_text())
            stats = data["stats"]

            # Count expected not-supported mutants
            expected_not_supported = sum(
                n_mut for stem, safe, n_mut in programs if not safe
            )
            assert stats["not_supported_mutants"] >= expected_not_supported, (
                f"Expected at least {expected_not_supported} not_supported_mutants, "
                f"got {stats['not_supported_mutants']}"
            )

    @given(programs=program_set())
    @settings(max_examples=100)
    def test_passed_safety_check_allows_kill_check(self, programs, tmp_path_factory):
        """Mutants of programs that PASS safety check ARE subjected to kill checking.

        Complementary check: ensures we don't accidentally skip everything.

        **Validates: Requirements 4.2, 4.3, 4.4**
        """
        tmp_path = tmp_path_factory.mktemp("eval")
        programs_dir, mutants_dir, mutants_with_tests_dir = _setup_filesystem(
            tmp_path, programs
        )

        safety_map = {stem: safe for stem, safe, _ in programs}
        kill_checked_mutants: list[str] = []

        def mock_safety_check(original: Path, test_file: Path, **kwargs) -> bool:
            return safety_map[original.stem]

        def mock_check_kill(test_file: Path, mutant_file: Path) -> MutantResult:
            kill_checked_mutants.append(mutant_file.name)
            return MutantResult(
                mutant_name=mutant_file.name,
                original_name=f"{mutant_file.stem.split('__')[0]}.dfy",
                status=MutantStatus.KILLED,
                execution_time=0.1,
            )

        mock_gen_instance = MagicMock()
        mock_gen_instance.name = "DafnyTestGenerator_Spec"

        def mock_generate_tests(dfy_file: Path, output_file: Path) -> TestGenResult:
            output_file.parent.mkdir(parents=True, exist_ok=True)
            output_file.write_text(f"// tests for {dfy_file.stem}")
            return TestGenResult(success=True, test_file=output_file)

        mock_gen_instance.generate_tests.side_effect = mock_generate_tests

        with (
            patch("src.runners.run_evaluation.SELECTED_PROGRAMS_DIR", programs_dir),
            patch("src.runners.run_evaluation.SELECTED_PROGRAMS_MUTANTS_DIR", mutants_dir),
            patch(
                "src.runners.run_evaluation.SELECTED_PROGRAMS_MUTANTS_WITH_TESTS_DIR",
                mutants_with_tests_dir,
            ),
            patch("src.runners.run_evaluation.run_safety_check", side_effect=mock_safety_check),
            patch("src.runners.run_evaluation.SpecTestGenerator", return_value=mock_gen_instance),
            patch("src.runners.run_evaluation.KillChecker") as mock_checker_cls,
        ):
            mock_checker = MagicMock()
            mock_checker.check_kill.side_effect = mock_check_kill
            mock_checker_cls.return_value = mock_checker

            output_dir = tmp_path / "results"
            run_pipeline(sequential=True, output_dir=output_dir)

        # Identify stems that passed safety
        passed_stems = {stem for stem, safe, _ in programs if safe}

        # All mutants of passed programs should have been kill-checked
        expected_checked = set()
        for stem, safe, n_mut in programs:
            if safe:
                for i in range(n_mut):
                    expected_checked.add(f"{stem}__{i}-{i+1}_CBE.dfy")

        actual_checked = set(kill_checked_mutants)
        assert expected_checked == actual_checked, (
            f"Expected kill-checked: {expected_checked}, got: {actual_checked}"
        )
