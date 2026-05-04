# Mutation Testing Evaluation

Evaluates test-generation strategies for Dafny programs using mutation testing.
Samples programs from DafnyBench, mutates them with MutDafny, generates tests
with a pluggable strategy, and measures kill rate.

## Quick Start (Docker)

```bash
# Submodules must be initialized before building
git submodule update --init --recursive

# Build from repo root
DOCKER_BUILDKIT=1 docker build -f Evaluation/Dockerfile -t mt-eval .
docker run --rm -it -w /app mt-eval bash
```

## Quick Start (Local)

```bash
# From repo root — init submodules (DafnyBench + MutDafny)
git submodule update --init --recursive

cd Evaluation
pip install -r requirements.txt
```

> **Note**: Submodules must be initialized from the **repo root** (not from `Evaluation/`).
> DafnyBench and MutDafny live under `Evaluation/external/` and won't be present without this step.

## Pipeline Overview

Two decoupled scripts:

1. **Dataset generation** — sample → verify originals → mutate → verify mutant fails → diffs
2. **Evaluation** — generate tests → run against mutants → report kill rate

### Generate a Dataset

```bash
python -m src.runners.generate_dataset --n-mutants 50 --output-dir dataset/data/my_run
```

Options:
- `--n-mutants N` — number of mutants (default 100)
- `--output-dir DIR` — where to write the dataset
- `--sequential` — disable parallelism, print per-file debug info

### Run Evaluation

```bash
python -m src.runners.run_evaluation dataset/data/my_run --output-dir results/
```

Options:
- `--clean-cache` — remove previous test/result artifacts before running
- `--sequential` — disable parallelism, print per-mutant debug info
- `--output-dir DIR` — where to write results JSON (default: dataset path)

### Output

Terminal summary table + `results.json` with per-mutant entries:

```
------------------------------------------------------------
   Total   Killed   Survived   Timeout  Kill Rate
------------------------------------------------------------
      50       38          9         3      82.6%
------------------------------------------------------------
```

## Adding a New Test Generation Strategy

The pipeline uses an abstract `TestGenerator` interface. To add a new strategy:

### 1. Create a new generator

Create a file in `src/mt_eval/generators/`, e.g. `my_generator.py`:

```python
from pathlib import Path
from src.mt_eval.core.abstract import TestGenerator, TestGenResult

class MyGenerator(TestGenerator):
    def __init__(self, **kwargs):
        super().__init__(name="MyGenerator", **kwargs)

    def generate_tests(self, dafny_file: Path, output_file: Path) -> TestGenResult:
        """Receive a .dfy file, produce a new .dfy file with tests.

        Args:
            dafny_file: Original verified Dafny program.
            output_file: Where to write the generated test file.

        Returns:
            TestGenResult with success=True and test_file set on success,
            or success=False with error_message on failure.
        """
        # Your logic here: invoke a tool, call an LLM, etc.
        # Write test code to output_file
        output_file.write_text("// generated tests\n")
        return TestGenResult(success=True, test_file=output_file)
```

The contract:
- **Input**: a verified `.dfy` file
- **Output**: a new `.dfy` file that can be run with `dafny run --no-verify`
- If the test file detects a mutation (non-zero exit), the mutant is **killed**
- If it passes (zero exit), the mutant **survived**

### 2. Write tests for your generator

Create `tests/unit/test_my_generator.py`:

```python
from unittest.mock import patch, MagicMock
from pathlib import Path
from src.mt_eval.generators.my_generator import MyGenerator
from src.mt_eval.core.abstract import TestGenResult

def test_generates_test_file(tmp_path):
    gen = MyGenerator()
    out = tmp_path / "test.dfy"
    result = gen.generate_tests(Path("input.dfy"), out)
    assert result.success
    assert result.test_file == out

def test_handles_failure(tmp_path):
    # Test your error paths
    ...
```

Run tests:

```bash
python -m pytest tests/ -v
```

### 3. Wire it into the evaluation runner

Edit `src/runners/run_evaluation.py` — replace `SpecTestGenerator()` with your generator,
or add a CLI flag to select the strategy:

```python
from src.mt_eval.generators.my_generator import MyGenerator
generator = MyGenerator()
```

### 4. Run evaluation with your strategy

```bash
python -m src.runners.run_evaluation dataset/data/my_run --sequential
```

The `--sequential` flag is useful for debugging — it prints per-mutant results to stdout.

## Repository Layout

```
Evaluation/
├── src/
│   ├── config.py                  # Paths, timeouts, env var overrides
│   ├── logging_config.py          # Centralized logging
│   ├── mt_eval/
│   │   ├── core/
│   │   │   ├── abstract.py        # TestGenerator ABC + TestGenResult
│   │   │   ├── models.py          # MutantResult, MutantStatus
│   │   │   ├── sampler.py         # Random program sampling
│   │   │   ├── verification.py    # dafny verify filter
│   │   │   └── mutation.py        # MutDafny invocation + diff
│   │   ├── execution/
│   │   │   ├── parallel_executor.py  # ThreadPoolExecutor + BoundedSemaphore
│   │   │   └── kill_checker.py       # dafny run --no-verify
│   │   ├── generators/
│   │   │   └── spec_test_generator.py  # SpecTestGenerator (default)
│   │   ├── metrics/
│   │   │   └── kill_rate.py       # Kill rate computation
│   │   └── reporting/
│   │       └── summary.py         # Stdout table + JSON output
│   └── runners/
│       ├── generate_dataset.py    # Dataset generation CLI
│       └── run_evaluation.py      # Evaluation CLI
├── dataset/
│   ├── scripts/                   # Shell helpers
│   └── data/                      # Generated datasets
├── tests/
│   ├── unit/                      # Unit + property tests
│   └── integration/               # End-to-end tests
├── external/                      # Git submodules (DafnyBench, MutDafny)
├── Dockerfile
├── requirements.txt
└── .repo_mutation_testing_marker
```

## Configuration

All configurable via environment variables:

| Variable | Default | Description |
|---|---|---|
| `MT_SAMPLE_COUNT` | 100 | Number of programs to sample |
| `MT_VERIFY_TIMEOUT` | 300 | Verification timeout (seconds) |
| `MT_TESTGEN_TIMEOUT` | 300 | Test generation timeout (seconds) |
| `MT_EXECUTION_TIMEOUT` | 300 | Kill check timeout (seconds) |
| `MT_MAX_JOBS` | cpu_count - 1 | Max parallel workers |
| `MT_LOG_LEVEL` | INFO | Logging level (DEBUG, INFO, WARNING, ERROR) |

## Running Tests

```bash
cd Evaluation
python -m pytest tests/ -v
```

Property-based tests use [Hypothesis](https://hypothesis.readthedocs.io/) with 100 iterations each.
