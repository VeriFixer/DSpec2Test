# DSpec2Test — Artifact Review Guide

This document provides instructions for artifact reviewers to reproduce the results of DSpec2Test using Docker.

**DSpec2Test** is a Dafny fork that adds a `Spec` mode to `dafny generate-tests`, generating tests from method/function specifications. The Spec mode generates tests for each method/function that fails to verify. Additionally, methods/functions tagged with `{:testEntry}` are always tested regardless of verification status. The `--bva` flag enables Boundary Value Analysis.

---

## 1. About DSpec2Test

Dafny's `generate-tests` command is an experimental feature that automatically generates tests for Dafny methods and/or functions tagged with the `{:testEntry}` label.

In Dafny's current implementation, there are 3 modes. In this fork, a fourth one was added (**Spec**), allowing generation of tests based solely on the method's/function's specification. This new integrated tool is called **DSpec2Test**.

---

## 2. Installation

Two installation paths are available. Docker is recommended for artifact reviewers as it avoids platform mismatches.

### Option A: Docker (recommended)

Everything pre-packaged: .NET SDK 8, Dafny (DSpec2Test), Z3 4.12.1, Java 17, Python 3, MutDafny, and the evaluation pipeline.

#### Using the pre-built image

A ready-to-use Docker image is provided as a `.tar.gz` archive (in the artifact submission):

```bash
docker load -i dspec2test.tar.gz
```

#### Building the image yourself

Only needed if the pre-built image is not available:

```bash
git submodule update --init --recursive
DOCKER_BUILDKIT=1 docker build -t dspec2test .
```

Build time: ~15–25 minutes (Z3 compiles from source). Requires ≥8GB Docker RAM.

#### Exporting the image as a tar.gz

To generate a portable image archive (e.g. for artifact submission):

```bash
docker save dspec2test | gzip > dspec2test.tar.gz
```

#### Starting the environment

Start an interactive session:

```bash
docker run --rm -it dspec2test
```

You are now inside the container at `/app`. The `dafny` binary is on PATH.

Verify the tool works:

```bash
dafny --version
```

All commands in the sections below (Demo Examples, Evaluation Pipeline, etc.) can be run directly in this shell session.

---

### Option B: Manual installation (from source)

#### Prerequisites

- .NET SDK 8
- Java 17
- Python 3 + venv
- Z3 4.12.1 (built with `--dotnet` for .NET bindings)

#### Clone with submodules

```bash
git clone --recursive <repo-url>
cd SpecTestGenerator
```

Or if already cloned:

```bash
git submodule update --init --recursive
```

#### Build from source

```bash
dotnet build Source/Dafny.sln -c Release
```

The `dafny` binary will be at `Binaries/Dafny`. Add it to PATH:

```bash
export PATH="$(pwd)/Binaries:$PATH"
```

---

### How to Run

Given a Dafny file with methods and/or functions, the **Spec** mode will attempt to generate tests for each of them that fails to verify. Additionally, one can flag methods/functions with `{:testEntry}` to oblige the tool to generate tests for them.

It is advised to run DSpec2Test with the `--length-limit X` flag, so that the length of sequences, sets, and maps in the generated tests are limited to a reasonable value.

---

## 3. Running DSpec2Test (Spec Mode with --bva)

### 3.1 Basic Usage

```bash
dafny generate-tests Spec <file.dfy> --bva
```

### 3.2 Demo 1: Classify (correct program)

The file is pre-loaded in the image at `/app/Example/Example1.dfy`:

```dafny
method {:testEntry} Classify(x: int) returns (r: int)
  ensures x < 0 ==> r == -1
  ensures x == 0 ==> r == 0
  ensures x > 0 ==> r == 1
{
  if x < 0 {
    r := -1;
  } else if x == 0 {
    r := 0;
  } else {
    r := 1;
  }
}
```

Run:

```bash
dafny generate-tests Spec /app/Example/Example1.dfy --bva
```

**Expected output** (test methods generated on stdout):

```dafny
include "/app/Example/Example1.dfy"
method {:test} Test0() {
var r0 := Classify(1);
expect 1 < 0 ==> r0 == -1;
expect 1 == 0 ==> r0 == 0;
expect 1 > 0 ==> r0 == 1;
}
method {:test} Test2() {
var r0 := Classify(100);
expect 100 < 0 ==> r0 == -1;
expect 100 == 0 ==> r0 == 0;
expect 100 > 0 ==> r0 == 1;
}
method {:test} Test6() {
var r0 := Classify(0);
expect 0 < 0 ==> r0 == -1;
expect 0 == 0 ==> r0 == 0;
expect 0 > 0 ==> r0 == 1;
}
method {:test} Test10() {
var r0 := Classify(-1);
expect -1 < 0 ==> r0 == -1;
expect -1 == 0 ==> r0 == 0;
expect -1 > 0 ==> r0 == 1;
}
method {:test} Test11() {
var r0 := Classify(-100);
expect -100 < 0 ==> r0 == -1;
expect -100 == 0 ==> r0 == 0;
expect -100 > 0 ==> r0 == 1;
}
```

> **Note**: Exact test values may vary depending on solver state. The structure (include + test module with test methods covering each branch + boundary values) is deterministic.

### 3.3 Demo 2: MatchFirst (buggy program)

The file is pre-loaded in the image at `/app/Example/Example2.dfy`:

```dafny
method MatchFirst(s1: seq<int>, s2: seq<int>) returns (isMatch: bool)
  ensures isMatch == (|s1| == 0 || |s2| == 0 || s1[0] == s2[0])
{
  return |s1| == 1 || |s2| == 0 || s1[0] == s2[0];
}
```

This program has a bug: the implementation uses `|s1| == 1` instead of `|s1| == 0`.

Run:

```bash
dafny generate-tests Spec /app/Example/Example2.dfy --bva
```

**Expected output** (generates failing tests that expose the bug):

```dafny
include "/app/Example/Example2.dfy"
method {:test} Test0() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [];
var r0 := MatchFirst(seqint0, seqint1);
expect r0 == (|seqint0| == 0 || |seqint1| == 0 || seqint0[0] == seqint1[0]);
}
method {:test} Test2() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [0];
var r0 := MatchFirst(seqint0, seqint1);
expect r0 == (|seqint0| == 0 || |seqint1| == 0 || seqint0[0] == seqint1[0]);
}
method {:test} Test3() {
var seqint0 : seq<int> := [];
var seqint1 : seq<int> := [0, 0];
var r0 := MatchFirst(seqint0, seqint1);
expect r0 == (|seqint0| == 0 || |seqint1| == 0 || seqint0[0] == seqint1[0]);
}
method {:test} Test8() {
var seqint0 : seq<int> := [0];
var seqint1 : seq<int> := [];
var r0 := MatchFirst(seqint0, seqint1);
expect r0 == (|seqint0| == 0 || |seqint1| == 0 || seqint0[0] == seqint1[0]);
}
method {:test} Test10() {
var seqint0 : seq<int> := [0, 0];
var seqint1 : seq<int> := [];
var r0 := MatchFirst(seqint0, seqint1);
expect r0 == (|seqint0| == 0 || |seqint1| == 0 || seqint0[0] == seqint1[0]);
}
method {:test} Test15() {
var seqint0 : seq<int> := [24];
var seqint1 : seq<int> := [24];
var r0 := MatchFirst(seqint0, seqint1);
expect r0 == (|seqint0| == 0 || |seqint1| == 0 || seqint0[0] == seqint1[0]);
}
method {:test} Test17() {
var seqint0 : seq<int> := [24, 0];
var seqint1 : seq<int> := [24];
var r0 := MatchFirst(seqint0, seqint1);
expect r0 == (|seqint0| == 0 || |seqint1| == 0 || seqint0[0] == seqint1[0]);
}
method {:test} Test19() {
var seqint0 : seq<int> := [24];
var seqint1 : seq<int> := [24, 0];
var r0 := MatchFirst(seqint0, seqint1);
expect r0 == (|seqint0| == 0 || |seqint1| == 0 || seqint0[0] == seqint1[0]);
}
method {:test} Test24() {
var seqint0 : seq<int> := [24];
var seqint1 : seq<int> := [25];
var r0 := MatchFirst(seqint0, seqint1);
expect r0 == (|seqint0| == 0 || |seqint1| == 0 || seqint0[0] == seqint1[0]);
}
method {:test} Test26() {
var seqint0 : seq<int> := [24, 0];
var seqint1 : seq<int> := [25];
var r0 := MatchFirst(seqint0, seqint1);
expect r0 == (|seqint0| == 0 || |seqint1| == 0 || seqint0[0] == seqint1[0]);
}
method {:test} Test28() {
var seqint0 : seq<int> := [24];
var seqint1 : seq<int> := [25, 0];
var r0 := MatchFirst(seqint0, seqint1);
expect r0 == (|seqint0| == 0 || |seqint1| == 0 || seqint0[0] == seqint1[0]);
}

```

> **Note**: The test with `s1 := []` exposes the bug — the spec says `isMatch` should be `true` (since `|s1| == 0`), but the implementation returns `false` (since `|s1| == 1` is false and `|s2| == 0` is false and `s1[0]` would be out of bounds).

### 3.4 Save Output to File

```bash
dafny generate-tests Spec /app/Example/Example1.dfy --bva > ClassifyTests.dfy
```

### 3.5 Additional Flags

This mode comes with 5 additional flags:

- `--simplify`: Simplifies test output by including only input and output values." +
  "In other words, removes 'expect' statements related to pre and post condition, whenever possible.");

- `--fdnf`: Calculates the full DNF, instead of the safe DNF (default). It produces all 2^N − 1 non-empty subsets of branch satisfaction. For A || B: branches A ∧ B, A ∧ !B, !A ∧ B.
  Generates more clauses (more test scenarios) but drops the short-circuit-safety guarantee: tests may evaluate guarded subexpressions where the guard is false, potentially causing runtime errors (e.g.: out-of-bounds, division by zero).

- `--bva`: Adds Boundary Value Analysis to test generation. Cannot be used simultaneously with `--repeat`.

- `--repeat`: Repeats the pipeline N times, in order to generate, approximately, N times more tests than the initial iteration. 1 (default) indicates no repetition. Cannot be used simultaneously with `--bva`.

- `--passing-failing`: Splits generated tests into passing and failing.

Example with multiple flags:

```bash
dafny generate-tests Spec /app/Example/Example1.dfy --bva --simplify --length-limit 5
```

---

## 4. Running the Evaluation Pipeline From cached results

The evaluation uses mutation testing to measure test-generation effectiveness.

### 4.1 Run Evaluation (Spec_bva Strategy)

```bash
cd /app/Evaluation
python -m src.runners.run_evaluation --strategies=Spec_bva
```

### 4.2 Run All Strategies

```bash
cd /app/Evaluation
python -m src.runners.run_evaluation --strategies=all
```

Available strategies: `Spec`, `Block`, `Spec_bva`

### 4.3 Expected Evaluation Output

Terminal output:

```
[run_evaluation] Cache hit for DafnyTestGenerator_Spec_bva, loading from results/results_DafnyTestGenerator_Spec_bva.json
Strategy                    | Kill Rate | Killed | Survived | Not-Supported Programs | Not-Supported Mutants
----------------------------+-----------+--------+----------+------------------------+----------------------
DafnyTestGenerator_Block    | 67.00%    | 134    | 54       | 0                      | 0                    
DafnyTestGenerator_Spec     | 54.44%    | 98     | 66       | 2                      | 20                   
DafnyTestGenerator_Spec_bva | 75.29%    | 128    | 25       | 3                      | 30                   
[run_evaluation] Comparison written to results/comparison.json

```

Results are written to:

```
/app/Evaluation/results/results/comparison.json
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

Expected output
```
========================================================================
Table 1: Mutation kill rates (top) and kill overlap (bottom)
on the 131 realistically-killable mutants.
Timeouts (TO) are runtime infinite loops introduced by the mutation
and credited as kills. The Killed column is FAIL + TO.
========================================================================

Strategy                FAIL    TO  Killed  Surv.   Kill%
---------------------------------------------------------
Block (WB)                99     9     108     23   82.4%
Spec_bva (BB)            106    17     123      8   93.9%
Union                      —     —     125      6   95.4%

Killed by both             —     —     106      —   80.9%
Killed by Block only       —     —       2      —    1.5%
Killed by Spec_bva only     —     —      17      —   13.0%
Killed by neither          —     —       6      —    4.6%

Denominator (realistically-killable): 131
Excluded: 22 incompetent + 17 equivalent = 39 (from 170 common mutants)
```

## 5 Reproduce Paper Results without cached Results

### 5.1 Generate mutants
Pre-generated mutants are included. To regenerate:

```bash
# Expected time around 30 minutes
cd /app/Evaluation
python -m src.runners.generate_mutants
```

You will see information for each mutated program testel like so (at the end this will show): 
```
Generating mutants (Active Cores:16): 100%|███████| 20/20 [00:53<00:00,  2.67s/file]
```
---

### 5.2 Run Pre manual analyses resulsts

To reproduce the full comparison table:

```bash
# Expected time around 1h-2h depending on the hardware
# takes ~1h in Intel(R) Core(TM) Ultra 9 285H
cd /app/Evaluation
python -m src.runners.run_evaluation --strategies=all --clean-cache
```

This produces `results/comparison.json` with kill rates for all strategies. At the end of the comment a equal table as the before presented on the cached results is shown.

Then apllying the manually-corrected results it should give the same results as the cached ones before.

```bash
cd /app/Evaluation
python results_after_manual_analysis.py
```

That gives the main results on the paper.
---

## 6. File Locations Inside the Container

| Path | Contents |
|------|----------|
| `/app/Binaries/Dafny` | DSpec2Test binary |
| `/app/Example/` | Demo programs (Example1.dfy, Example2.dfy) |
| `/app/Evaluation/dataset/selected_programs/` | 20 benchmark Dafny programs |
| `/app/Evaluation/dataset/selected_programs_mutants/` | Pre-generated mutants |
| `/app/Evaluation/results/` | Evaluation results (JSON) |
| `/app/Evaluation/src/` | Pipeline source code |

---