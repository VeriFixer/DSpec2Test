# Evaluation Pipeline — Quick Guide

## Prerequisites

1. **Python deps**:
   ```bash
   cd Evaluation
   pip install -r requirements.txt
   ```

2. **Build MutDafny** (required for mutant generation):
   ```bash
   git submodule update --init --recursive
   cd Evaluation/external/mutation/mutdafny/mutdafny
   dotnet build
   ```
   This produces the `mutdafny.dll` plugin used by `generate_mutants.py`.

3. **Dafny binary**: The pipeline expects a Dafny binary at `Binaries/Dafny` (repo root). You can override it with the env var `MT_SPECTEST_BINARY`.

> **Note**: The `Dockerfile` exists but is **untested** for now. Use local setup.

---

## Generating mutatns
need to change directoy to the Evaluation repo

```bash
python -m src.runners.generate_mutants
```
## Running the Evaluation

From the `Evaluation/` directory:

```bash
# Run all strategies (Spec + Block)
python -m src.runners.run_evaluation

# Run only Spec strategy
python -m src.runners.run_evaluation --strategies=Spec 

# Force re-run (clear cached results)
python -m src.runners.run_evaluation --clean-cache 
```

The `--sequential` flag is recommended for debugging (prints progress per-mutant). Without it, tasks run in parallel.

---

## Where Results Appear

After a run, look in:

```
Evaluation/results/
├── results_DafnyTestGenerator_Spec.json    # Per-strategy detailed results
├── results_DafnyTestGenerator_Block.json   # Per-strategy detailed results
└── comparison.json                         # Side-by-side kill rates
```

Each results JSON contains:
- `stats.kill_rate` — fraction of supported mutants killed
- `stats.killed` / `stats.survived` — counts
- `stats.not_supported_programs` — programs where test gen or safety check failed
- `results` — per-mutant details (status, execution time, commands used)

The `comparison.json` shows which strategy had the best kill rate.

Combined test+mutant files (for manual inspection) are at:
```
Evaluation/dataset/selected_programs_mutants_with_tests_Spec/
Evaluation/dataset/selected_programs_mutants_with_tests_Block/
```

---

## Changing Strategy Commands

Each strategy builds its own `dafny generate-tests` command. To change parameters (test count, length limit, etc.), edit the `_build_cmd` method in the corresponding file:

- **Spec strategy**: `Evaluation/src/mt_eval/generators/spec_test_generator.py`
- **Block strategy**: `Evaluation/src/mt_eval/generators/block_test_generator.py`

Example — the Block strategy command:

```python
def _build_cmd(self, dafny_file: Path) -> list[str]:
    return [
        str(self.dafny_binary),
        "generate-tests",
        "Block",
        str(dafny_file.resolve()),
        "--test-count", "1",       # ← change this
        "--length-limit", "50",    # ← or this
        "--ignore-warnings",
    ]
```

Just edit the list and re-run. No other wiring needed.

---

## What to Expect

- **Kill rate** is the main metric: what % of mutants does the strategy detect.
- Programs where test generation fails or the safety check fails are marked "not supported" and their mutants are excluded from the kill rate calculation.
- A mutant is **killed** if running the generated tests against it produces a non-zero exit code (runtime assertion violation, etc.).
- A mutant **survives** if the tests pass on it (zero exit code) — meaning the tests couldn't distinguish it from the original.
- Higher kill rate = better test generation strategy.

---

## Generating Mutants (if needed)

If `dataset/selected_programs_mutants/` is empty or you want fresh mutants:

```bash
python -m src.runners.generate_mutants --sequential
```

This uses MutDafny to generate mutants from the 20 programs in `dataset/selected_programs/`.
