"""Property-based tests for generate_mutants module.

Feature: pipeline-rework, Property 1: File collection returns only .dfy files
Feature: pipeline-rework, Property 2: Mutant verification filter keeps only failing mutants
"""

import sys
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest
from hypothesis import given, settings, assume
from hypothesis import strategies as st

from src.runners.generate_mutants import collect_programs, _process_program


# Strategy: generate filenames with various extensions
_safe_stem = st.from_regex(r"[a-z][a-z0-9_]{0,12}", fullmatch=True)
_dfy_ext = st.just(".dfy")
_non_dfy_ext = st.sampled_from([".py", ".txt", ".java", ".cs", ".md", ".json", ".dfy.bak", ""])
_dfy_file = st.builds(lambda s: s + ".dfy", _safe_stem)
_non_dfy_file = st.builds(lambda s, e: s + e, _safe_stem, _non_dfy_ext)


@given(
    dfy_names=st.lists(_dfy_file, min_size=1, max_size=20, unique=True),
    non_dfy_names=st.lists(_non_dfy_file, min_size=0, max_size=20, unique=True),
)
@settings(max_examples=100)
def test_collect_programs_returns_only_dfy_sorted(dfy_names, non_dfy_names, tmp_path_factory):
    """Property 1: For any directory with mixed files, collect_programs returns
    exactly the .dfy files, sorted, and no others.

    **Validates: Requirements 1.1**
    """
    tmp_path = tmp_path_factory.mktemp("collect")

    # Create .dfy files
    for name in dfy_names:
        (tmp_path / name).touch()

    # Create non-.dfy files
    for name in non_dfy_names:
        # Skip if name accidentally ends with .dfy
        if not name.endswith(".dfy"):
            (tmp_path / name).touch()

    result = collect_programs(tmp_path)

    # Only .dfy files returned
    assert all(p.suffix == ".dfy" for p in result)

    # Sorted
    assert result == sorted(result)

    # Exactly the .dfy files we created
    expected = sorted(tmp_path / n for n in dfy_names)
    assert result == expected


def test_collect_programs_empty_directory_exits(tmp_path):
    """Edge case: empty directory causes SystemExit.

    **Validates: Requirements 1.1**
    """
    with pytest.raises(SystemExit):
        collect_programs(tmp_path)


def test_collect_programs_no_dfy_files_exits(tmp_path):
    """Edge case: directory with files but no .dfy causes SystemExit.

    **Validates: Requirements 1.1**
    """
    (tmp_path / "readme.md").touch()
    (tmp_path / "script.py").touch()
    with pytest.raises(SystemExit):
        collect_programs(tmp_path)


# --- Property 2: Mutant verification filter keeps only failing mutants ---

# Strategy: generate mutant paths and corresponding verify outcomes
_mutant_path = st.builds(
    lambda stem: Path(f"/tmp/mutants/{stem}.dfy"),
    st.from_regex(r"[a-z][a-z0-9_]{0,8}", fullmatch=True),
)


@given(
    outcomes=st.lists(
        st.tuples(
            st.from_regex(r"[a-z][a-z0-9_]{0,8}", fullmatch=True),
            st.booleans(),
        ),
        min_size=1,
        max_size=30,
        unique_by=lambda t: t[0],
    )
)
@settings(max_examples=100)
def test_verification_filter_keeps_only_failing_mutants(outcomes):
    """Property 2: For any list of mutant paths with arbitrary verification outcomes,
    the pipeline SHALL include only those mutants where verify_program returns False.

    **Validates: Requirements 2.3**
    """
    # Build mutant paths and verify outcomes
    mutant_paths = [Path(f"/tmp/mutants/{stem}.dfy") for stem, _ in outcomes]
    verify_results = {path: outcome for path, (_, outcome) in zip(mutant_paths, outcomes)}

    program = Path("/tmp/programs/original.dfy")
    output_dir = Path("/tmp/output")

    with patch("src.runners.generate_mutants.apply_mutation", return_value=mutant_paths), \
         patch("src.runners.generate_mutants.verify_program", side_effect=lambda m: verify_results[m]):
        stem, valid_mutants = _process_program(program, output_dir, max_mutants=10)

    # Only mutants where verify returned False should be kept
    expected = [p for p, (_, v) in zip(mutant_paths, outcomes) if not v]
    assert valid_mutants == expected
    assert all(not verify_results[m] for m in valid_mutants)
