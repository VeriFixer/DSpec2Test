# Mutation Testing Evaluation

Evaluates test-generation strategies for Dafny programs using mutation testing.
Uses a fixed set of 20 programs in `dataset/selected_programs/`, generates mutants
with MutDafny, runs a safety check on originals, then measures kill rate per strategy.

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
# From repo root — init submodules (MutDafny)
git submodule update --init --recursive

cd Evaluation
pip install -r requirements.txt
```

> **Note**: Submodules must be initialized from the **repo root** (not from `Evaluation/`).
> MutDafny lives under `Evaluation/external/` and won't be present without this step.

## Pipeline Overview

Two decoupled scripts operating on the fixed 20 programs:

1. **Mutant Generation** (`generate_mutants.py`) — collect programs → generate mutants via MutDafny → filter (keep only verify-failing) → write to `selected_programs_mutants/`
2. **Evaluation** (`run_evaluation.py`) — for each strategy: generate tests on original → safety check → kill check mutants → report statistics

### Generate Mutants

```bash
python -m src.runners.generate_mutants [--n-mutants-per-program N] [--sequential]
```

Options:
- `--n-mutants-per-program N` — max mutants to generate per program (default: 10)
- `--sequential` — disable parallelism

This reads `.dfy` files from `dataset/selected_programs/`, generates mutants, filters out any that still pass `dafny verify` (not real bugs), and writes valid mutants to `dataset/selected_programs_mutants/`.

### Run Evaluation

```bash
python -m src.runners.run_evaluation [--sequential] [--output-dir DIR] [--verbose] [--max-display N] [--strategies STRATEGIES] [--clean-cache]
```

Options:
- `--sequential` — disable parallelism, useful for debugging
- `--output-dir DIR` — where to write results JSON (default: `results/`)
- `--verbose` — print per-mutant details after summary (test gen command, kill check output)
- `--max-display N` — limit verbose output to N mutants (default: all)
- `--strategies STRATEGIES` — comma-separated strategy modes to run, or `"all"` (default: `all`). Available: `Spec`, `Block`
- `--clean-cache` — delete cached per-strategy results and combined dirs before running

No positional arguments — reads originals from `dataset/selected_programs/` and mutants from `dataset/selected_programs_mutants/` automatically.

#### Multi-Strategy Support

The pipeline supports multiple test-generation strategies (Spec, Block) running in a single invocation. Each strategy writes to isolated output directories:

- Combined test files: `dataset/selected_programs_mutants_with_tests_{Mode}/`
- Per-strategy results: `results/results_{strategy_name}.json`
- Comparison summary: `results/comparison.json`

**Caching**: If a per-strategy results file already exists, that strategy is skipped and results loaded from disk. Use `--clean-cache` to force re-execution.

Examples:

```bash
# Run all strategies (Spec + Block)
python -m src.runners.run_evaluation --sequential

# Run only Block strategy
python -m src.runners.run_evaluation --strategies=Block

# Run both, clearing previous results first
python -m src.runners.run_evaluation --clean-cache

# Run Spec only, custom output dir
python -m src.runners.run_evaluation --strategies=Spec --output-dir my_results/
```

### Output

Terminal summary + `results.json`:

```
============================================================
  Strategy: SpecTestGenerator
============================================================
  Programs: 20 total
    Supported:     18
    Not-supported: 2 (10.0%)
      - prog_a.dfy: test_generation_failed (10 mutants skipped)
      - prog_b.dfy: safety_check_failed (10 mutants skipped)
  Mutants: 180 total
    Supported:     160
    Not-supported: 20 (11.1%)
  Kill results (supported only):
    Killed:   130
    Survived: 28
    Timeout:  1
    Error:    1
  Kill rate: 81.25%
============================================================
```

With `--verbose`:

```
────────────────────────────────────────────────────────────────
  VERBOSE: Per-mutant details (3/160 shown)
────────────────────────────────────────────────────────────────

  [✗ KILLED] prog__10-20_AOR.dfy (4.2s)
    Original: prog.dfy
    Test gen: /path/to/dafny generate-tests Spec ...
    Kill cmd: /path/to/dafny run --no-verify --allow-warnings ...
    stderr: Runtime assertion violation

  [✓ SURVIVED] prog__30-40_CBE.dfy (3.8s)
    Original: prog.dfy
    Test gen: /path/to/dafny generate-tests Spec ...
    Kill cmd: /path/to/dafny run --no-verify --allow-warnings ...

────────────────────────────────────────────────────────────────
```

JSON output (`results/results_DafnyTestGenerator_Spec.json`):

```json
{
  "strategy": "DafnyTestGenerator_Spec",
  "stats": {
    "total_programs": 20,
    "not_supported_programs": 2,
    "not_supported_program_rate": 0.10,
    "total_mutants": 180,
    "not_supported_mutants": 18,
    "not_supported_mutant_rate": 0.10,
    "supported_mutants": 162,
    "killed": 130,
    "survived": 28,
    "timeout": 3,
    "error": 1,
    "kill_rate": 0.8025
  },
  "results": [...]
}
```

Comparison output (`results/comparison.json`):

```json
{
  "strategies": {
    "DafnyTestGenerator_Spec": { "kill_rate": 0.8025, "killed": 130, ... },
    "DafnyTestGenerator_Block": { "kill_rate": 0.65, "killed": 105, ... }
  },
  "best_kill_rate": "DafnyTestGenerator_Spec"
}
```

## Adding a New Test Generation Strategy

The pipeline uses a `DafnyTestGenerator` base class for Dafny-based strategies, and an abstract `TestGenerator` interface for custom generators.

### Adding a Dafny mode strategy

If your strategy is a new `dafny generate-tests` mode, just create a thin subclass:

```python
# src/mt_eval/generators/my_mode_generator.py
from src.mt_eval.generators.dafny_test_generator import DafnyTestGenerator

class MyModeGenerator(DafnyTestGenerator):
    def __init__(self, **kwargs):
        super().__init__(mode="MyMode", **kwargs)
```

Then register it in `src/mt_eval/generators/__init__.py`:

```python
from src.mt_eval.generators.my_mode_generator import MyModeGenerator

STRATEGY_REGISTRY["MyMode"] = MyModeGenerator
```

Now `--strategies=MyMode` works automatically.

### Adding a non-Dafny strategy

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
        output_file.write_text("// generated tests\n")
        return TestGenResult(success=True, test_file=output_file)
```

The contract:
- **Input**: a verified `.dfy` file
- **Output**: a new `.dfy` file containing the original source + test methods appended at the bottom
- Kill checking builds a combined file: mutant source + test methods, saved in `selected_programs_mutants_with_tests/`
- If the combined file fails (non-zero exit from `dafny run --no-verify`), the mutant is **killed**
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

### 3. Register and wire it

Add to `src/mt_eval/generators/__init__.py`:

```python
from src.mt_eval.generators.my_generator import MyGenerator

STRATEGY_REGISTRY["MyGen"] = MyGenerator
```

### 4. Run evaluation with your strategy

```bash
python -m src.runners.run_evaluation --strategies=MyGen --sequential
```

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
│   │   │   ├── verification.py    # dafny verify filter
│   │   │   └── mutation.py        # MutDafny invocation + diff
│   │   ├── execution/
│   │   │   ├── parallel_executor.py  # ThreadPoolExecutor + BoundedSemaphore
│   │   │   ├── kill_checker.py       # dafny run --no-verify (kill check)
│   │   │   └── safety_check.py      # dafny run --no-verify (safety check on original)
│   │   ├── generators/
│   │   │   ├── __init__.py            # Strategy registry + resolve_strategies()
│   │   │   ├── dafny_test_generator.py  # DafnyTestGenerator base class
│   │   │   ├── spec_test_generator.py   # SpecTestGenerator (mode="Spec")
│   │   │   └── block_test_generator.py  # BlockTestGenerator (mode="Block")
│   │   ├── metrics/
│   │   │   └── pipeline_stats.py  # PipelineStats dataclass
│   │   ├── paths.py               # Per-strategy path derivation utilities
│   │   └── reporting/
│   │       ├── summary.py         # Stdout table + JSON output
│   │       └── comparison.py      # Multi-strategy comparison table + JSON
│   └── runners/
│       ├── generate_mutants.py    # Mutant generation CLI
│       └── run_evaluation.py      # Evaluation CLI
├── dataset/
│   ├── selected_programs/              # Fixed 20 input programs
│   ├── selected_programs_mutants/      # Generated killed mutants (output of generate_mutants)
│   ├── selected_programs_mutants_with_tests_Spec/   # Combined files for Spec strategy
│   └── selected_programs_mutants_with_tests_Block/  # Combined files for Block strategy
├── results/
│   ├── results_DafnyTestGenerator_Spec.json   # Per-strategy results
│   ├── results_DafnyTestGenerator_Block.json  # Per-strategy results
│   └── comparison.json            # Cross-strategy comparison
├── tests/
│   ├── unit/                      # Unit + property tests
│   └── integration/               # End-to-end tests
├── external/                      # Git submodules (MutDafny)
├── Dockerfile
├── requirements.txt
└── .repo_mutation_testing_marker
```

## Manual Analysis (Post-Evaluation)

After running the regular evaluation pipeline, a **manual analysis** is required to produce
the final corrected results used in the paper. The raw kill rates include noise from:

1. **Incompetent mutants** — don't compile (resolution/type errors). Both tools spuriously
   report these as "killed" (non-zero exit from build failure).
2. **Equivalent mutants** — semantically identical to the original. No test can distinguish them.
3. **Timeouts** — all confirmed to be runtime infinite loops (loop-guard mutations on monotonic
   counters). These are reclassified as kills.

The manual classification for each of the 170 common mutants (Block ∩ Spec\_bva scope) is stored in:

```
results/manually_analysis.json
```

Each entry contains the original raw status from both tools, the corrected per-tool status
(timeout → killed), and the manual classification (`incompetent`, `equivalent`, `killed`,
`killed_timeout`, or `survived`).

To produce the final corrected results table (Table 1 in the paper):

```bash
cd Evaluation
python results_after_manual_analysis.py
```

This outputs the kill rates on the 131 realistically-killable mutants (after removing
22 incompetent + 17 equivalent), with timeouts folded into kills.

## Configuration

All configurable via environment variables:

| Variable | Default | Description |
|---|---|---|
| `MT_VERIFY_TIMEOUT` | 300 | Verification timeout (seconds) |
| `MT_TESTGEN_TIMEOUT` | 300 | Test generation timeout (seconds) |
| `MT_EXECUTION_TIMEOUT` | 300 | Kill check / safety check timeout (seconds) |
| `MT_MAX_JOBS` | cpu_count - 1 | Max parallel workers |
| `MT_LOG_LEVEL` | INFO | Logging level (DEBUG, INFO, WARNING, ERROR) |

## Running Tests

```bash
cd Evaluation
python -m pytest tests/ -v
```

Property-based tests use [Hypothesis](https://hypothesis.readthedocs.io/) with 100 iterations each.
