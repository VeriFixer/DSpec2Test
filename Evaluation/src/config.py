"""Central configuration for Mutation Testing Evaluation pipeline.

Marker-based root discovery, path constants, configurable params with env overrides.

Environment Variables (all optional):
    MT_SAMPLE_COUNT: Override SAMPLE_COUNT (default: 100)
    MT_VERIFY_TIMEOUT: Override VERIFY_TIMEOUT (default: 300)
    MT_TESTGEN_TIMEOUT: Override TESTGEN_TIMEOUT (default: 300)
    MT_EXECUTION_TIMEOUT: Override EXECUTION_TIMEOUT (default: 300)
    MT_MAX_JOBS: Override MAX_JOBS (default: cpu_count()-1, min 1)
    MT_MAX_MEMORY_MB: Override DAFNY_MAX_MEMORY_MB (default: 0.75 * total RAM)
"""

from pathlib import Path
import os
from multiprocessing import cpu_count

import psutil


def find_repo_root(marker: str = ".repo_mutation_testing_marker") -> Path:
    """Walk up from this file looking for the marker file.

    Args:
        marker: Filename to search for.

    Returns:
        Path to the directory containing the marker.

    Raises:
        FileNotFoundError: If marker not found traversing up from __file__.
    """
    current: Path = Path(__file__).resolve().parent
    while str(current) != current.root:
        if (current / marker).exists():
            return current
        current = current.parent
    raise FileNotFoundError(
        f"Could not find '{marker}'. Ensure you're running inside the Evaluation repo."
    )


# === Repository Structure ===
BASE_PATH: Path = find_repo_root()
DATASET_ROOT: Path = BASE_PATH / "dataset" / "data"
EXTERNAL_ROOT: Path = BASE_PATH / "external"
TMP_ROOT: Path = BASE_PATH / "tmp"
ARTIFACTS_ROOT: Path = TMP_ROOT / "run_artifacts"
SELECTED_PROGRAMS_DIR: Path = BASE_PATH / "dataset" / "selected_programs"
SELECTED_PROGRAMS_MUTANTS_DIR: Path = BASE_PATH / "dataset" / "selected_programs_mutants"
SELECTED_PROGRAMS_MUTANTS_WITH_TESTS_DIR: Path = BASE_PATH / "dataset" / "selected_programs_mutants_with_tests"

# === Dafny Binary ===
DAFNY_BINARY: Path = BASE_PATH.parent / "Binaries" / "Dafny"

# === SpecTestGenerator Binary (separate fork with Spec mode support) ===
SPECTEST_DAFNY_BINARY: Path = Path(
    os.environ.get(
        "MT_SPECTEST_BINARY",
        str(BASE_PATH.parent / "Binaries" / "Dafny"),
    )
)

# === MutDafny Plugin ===
MUTDAFNY_DIR: Path = EXTERNAL_ROOT / "mutation" / "mutdafny"
MUTDAFNY_PLUGIN: Path = MUTDAFNY_DIR / "mutdafny" / "bin" / "Debug" / "net8.0" / "mutdafny.dll"
# MutDafny must use its own bundled Dafny (version-coupled to the plugin)
MUTDAFNY_DAFNY_BINARY: Path = MUTDAFNY_DIR / "dafny" / "Binaries" / "Dafny"

# === Configurable Parameters (with env var overrides) ===
SAMPLE_COUNT: int = int(os.environ.get("MT_SAMPLE_COUNT", "100"))
VERIFY_TIMEOUT: int = int(os.environ.get("MT_VERIFY_TIMEOUT", "1500"))
TESTGEN_TIMEOUT: int = int(os.environ.get("MT_TESTGEN_TIMEOUT", "1500"))
EXECUTION_TIMEOUT: int = int(os.environ.get("MT_EXECUTION_TIMEOUT", "300"))
MAX_JOBS: int = max(1, int(os.environ.get("MT_MAX_JOBS", str(max(cpu_count() - 1, 1)))))

# === Memory Limit for Dafny/Z3 solver (MB) ===
# Default: 75% of total system RAM. Override with MT_MAX_MEMORY_MB env var.
_total_ram_mb = psutil.virtual_memory().total // (1024 * 1024)
DAFNY_MAX_MEMORY_MB: int = int(os.environ.get(
    "MT_MAX_MEMORY_MB",
    str(int(_total_ram_mb * 0.75)),
))