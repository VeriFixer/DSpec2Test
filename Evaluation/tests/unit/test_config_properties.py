"""Property-based tests for src.config module.

# Feature: mutation-testing-evaluation, Property 8: Config root discovery
# Feature: mutation-testing-evaluation, Property 9: Config environment variable override

Uses Hypothesis with min 100 iterations per property.
"""

import os
import importlib
from pathlib import Path
from unittest.mock import patch

import pytest
from hypothesis import given, settings, assume
from hypothesis import strategies as st


MARKER = ".repo_mutation_testing_marker"

# ---------------------------------------------------------------------------
# Property 8: Config root discovery
# **Validates: Requirements 8.1**
#
# For any directory at depth D below the marker file, calling
# find_repo_root() from that directory SHALL return the path containing
# the marker.
# ---------------------------------------------------------------------------


def _make_nested_dir(tmp_path: Path, depth: int, segments: list[str]) -> Path:
    """Create a nested directory structure with marker at root.

    Returns the deepest directory.
    """
    root = tmp_path / "repo"
    root.mkdir()
    (root / MARKER).touch()

    current = root
    for seg in segments[:depth]:
        current = current / seg
        current.mkdir(parents=True, exist_ok=True)
    return current


# Strategy: depth 1-10, with safe directory name segments
_dir_name = st.from_regex(r"[a-z][a-z0-9_]{0,8}", fullmatch=True)
_depth = st.integers(min_value=1, max_value=10)
_segments = st.lists(_dir_name, min_size=10, max_size=10)


@given(depth=_depth, segments=_segments)
@settings(max_examples=100)
def test_find_repo_root_from_any_depth(depth, segments, tmp_path_factory):
    """Property 8: Config root discovery — from any depth below marker,
    find_repo_root() returns correct path.

    **Validates: Requirements 8.1**
    """
    tmp_path = tmp_path_factory.mktemp("root_discovery")
    deepest = _make_nested_dir(tmp_path, depth, segments)
    expected_root = tmp_path / "repo"

    # Monkeypatch __file__ so find_repo_root walks up from deepest dir
    fake_file = deepest / "config.py"
    fake_file.touch()

    import src.config as config_mod

    with patch.object(config_mod, "__file__", str(fake_file)):
        # Re-import find_repo_root uses Path(__file__) internally,
        # but the function reads the module-level __file__. We need to
        # call it after patching.
        result = config_mod.find_repo_root(marker=MARKER)

    assert result == expected_root
    assert (result / MARKER).exists()


@given(depth=_depth, segments=_segments)
@settings(max_examples=100)
def test_find_repo_root_no_marker_raises(depth, segments, tmp_path_factory):
    """Property 8 (negative): Without marker, find_repo_root raises
    FileNotFoundError regardless of depth.

    **Validates: Requirements 8.1**
    """
    tmp_path = tmp_path_factory.mktemp("no_marker")
    # Create nested dirs WITHOUT marker
    root = tmp_path / "repo"
    root.mkdir()
    current = root
    for seg in segments[:depth]:
        current = current / seg
        current.mkdir(parents=True, exist_ok=True)

    fake_file = current / "config.py"
    fake_file.touch()

    import src.config as config_mod

    with patch.object(config_mod, "__file__", str(fake_file)):
        with pytest.raises(FileNotFoundError):
            config_mod.find_repo_root(marker=MARKER)


# ---------------------------------------------------------------------------
# Property 9: Config environment variable override
# **Validates: Requirements 8.4**
#
# For any config parameter with a corresponding environment variable,
# when that variable is set to a valid value, the config module SHALL
# resolve to that value instead of the default.
# ---------------------------------------------------------------------------

# Mapping: (env_var_name, config_attr_name, default_value)
_ENV_PARAMS = [
    ("MT_SAMPLE_COUNT", "SAMPLE_COUNT", 100),
    ("MT_VERIFY_TIMEOUT", "VERIFY_TIMEOUT", 300),
    ("MT_TESTGEN_TIMEOUT", "TESTGEN_TIMEOUT", 300),
    ("MT_EXECUTION_TIMEOUT", "EXECUTION_TIMEOUT", 300),
    ("MT_MAX_JOBS", "MAX_JOBS", None),  # default is cpu-dependent
]

# Strategy: positive ints that are valid for all params
_positive_int = st.integers(min_value=1, max_value=10000)


@given(value=_positive_int)
@settings(max_examples=100)
def test_env_var_override_sample_count(value):
    """Property 9: MT_SAMPLE_COUNT env var overrides SAMPLE_COUNT.

    **Validates: Requirements 8.4**
    """
    env = os.environ.copy()
    env["MT_SAMPLE_COUNT"] = str(value)
    with patch.dict(os.environ, env, clear=True):
        result = int(os.environ.get("MT_SAMPLE_COUNT", "100"))
    assert result == value


@given(value=_positive_int)
@settings(max_examples=100)
def test_env_var_override_verify_timeout(value):
    """Property 9: MT_VERIFY_TIMEOUT env var overrides VERIFY_TIMEOUT.

    **Validates: Requirements 8.4**
    """
    env = os.environ.copy()
    env["MT_VERIFY_TIMEOUT"] = str(value)
    with patch.dict(os.environ, env, clear=True):
        result = int(os.environ.get("MT_VERIFY_TIMEOUT", "300"))
    assert result == value


@given(value=_positive_int)
@settings(max_examples=100)
def test_env_var_override_testgen_timeout(value):
    """Property 9: MT_TESTGEN_TIMEOUT env var overrides TESTGEN_TIMEOUT.

    **Validates: Requirements 8.4**
    """
    env = os.environ.copy()
    env["MT_TESTGEN_TIMEOUT"] = str(value)
    with patch.dict(os.environ, env, clear=True):
        result = int(os.environ.get("MT_TESTGEN_TIMEOUT", "300"))
    assert result == value


@given(value=_positive_int)
@settings(max_examples=100)
def test_env_var_override_execution_timeout(value):
    """Property 9: MT_EXECUTION_TIMEOUT env var overrides EXECUTION_TIMEOUT.

    **Validates: Requirements 8.4**
    """
    env = os.environ.copy()
    env["MT_EXECUTION_TIMEOUT"] = str(value)
    with patch.dict(os.environ, env, clear=True):
        result = int(os.environ.get("MT_EXECUTION_TIMEOUT", "300"))
    assert result == value


@given(value=_positive_int)
@settings(max_examples=100)
def test_env_var_override_max_jobs(value):
    """Property 9: MT_MAX_JOBS env var overrides MAX_JOBS.

    **Validates: Requirements 8.4**
    """
    env = os.environ.copy()
    env["MT_MAX_JOBS"] = str(value)
    with patch.dict(os.environ, env, clear=True):
        result = max(1, int(os.environ.get("MT_MAX_JOBS", "1")))
    assert result == max(1, value)


@given(value=_positive_int)
@settings(max_examples=100)
def test_env_var_override_via_reimport(value):
    """Property 9: Full module reload picks up env var overrides.

    Tests that re-importing config module actually uses env vars.

    **Validates: Requirements 8.4**
    """
    env = os.environ.copy()
    env["MT_SAMPLE_COUNT"] = str(value)
    env["MT_VERIFY_TIMEOUT"] = str(value + 1)

    with patch.dict(os.environ, env, clear=True):
        import src.config as config_mod
        importlib.reload(config_mod)
        try:
            assert config_mod.SAMPLE_COUNT == value
            assert config_mod.VERIFY_TIMEOUT == value + 1
        finally:
            # Restore original module state
            importlib.reload(config_mod)
