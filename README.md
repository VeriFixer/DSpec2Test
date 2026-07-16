# DSpec2Test — Artifact Review Guide

This repository contains the artifact for **DSpec2Test**, a Dafny specification-based test generation tool.

This README is divided into two parts as per the ASE Artifact Evaluation guidelines:
1. **Part I: Getting Started Guide** (Artifact description, installation, and a smoke test taking < 30 minutes).
2. **Part II: Step-by-Step Instructions** (Detailed reproduction of paper claims and advanced tool usage).

---

**Note on Extended Evaluation:**

> Since the paper's acceptance, we have expanded our evaluation dataset from 20 programs to over 200 programs and released a new version of the tool. To ensure strict reproducibility of the accepted paper, this README.md, the architecture-specific images (`dspec2test-amd64.tar.gz` and `dspec2test-arm64.tar.gz`), and the source code archive (`dspec2test.zip`) are strictly dedicated to reproducing the **original claims**.
>
> Reviewers interested in the expanded evaluation can refer to [README_EXTENDED.md](https://github.com/VeriFixer/DSpec2Test/blob/generate-tests/spec/README_EXTENDED.md) and the corresponding architecture-specific (`dspec2test-amd64-extended.tar.gz` and `dspec2test-arm64-extended.tar.gz`) images.

All `.tar.gz` files are present in the latest release of the [repository](https://github.com/VeriFixer/DSpec2Test).

---

## Part I: Getting Started Guide

### 1. Artifact Description
**DSpec2Test** is a Dafny fork that adds a `Spec` mode to `dafny generate-tests`, generating tests purely from method/function specifications. The `Spec` mode generates tests for each method/function that fails to verify, or that is flagged with the `{:testEntry}` attribute. It supports Equivalence Class Partitioning (ECP) through Disjunctive Normal Form (DNF) and, optionally Boundary Value Analysis (BVA).

### 2. Installation Instructions

> **Prerequisite:** Docker must be installed on your system. See the [official Docker installation guide](https://docs.docker.com/get-docker/) for instructions.

**Step A: Load the pre-built image:**

We have provided a ready-to-use Docker archive built exactly from the paper's commit (`9f910cf907ef7ab252a0f957e253f9b23d5b9e53`). Ensure Docker is installed and running, then load the archive that matches your system's architecture:

```bash
# For x86_64 / AMD64 systems (Most Intel/AMD PCs):
docker load -i dspec2test-amd64.tar.gz

# For ARM64 systems (Apple Silicon M-series, ARM-based Linux):
docker load -i dspec2test-arm64.tar.gz
```

**[Optional]** If you wish to build the image from scratch, we have provided `dspec2test.zip`. This archive contains the exact source code from the paper's commit (`9f910cf907ef7ab252a0f957e253f9b23d5b9e53`), alongside a slightly modified `Dockerfile` and a new `.dockerignore` to ensure smooth cross-platform builds.
Building takes ~15–25 mins (Z3 compiles from source) and requires ≥ 8GB RAM:

1. Extract the archive and navigate into it:

```bash
unzip dspec2test.zip
cd dspec2test
```

2. Build the image according to your OS:

 - On Linux / macOS (Bash/Zsh):

    ```bash
    DOCKER_BUILDKIT=1 docker build -t dspec2test .
    ```

 - On Windows (PowerShell):

    ```bash
    $env:DOCKER_BUILDKIT=1; docker build -t dspec2test .
    ```

 - On Windows (Command Prompt / cmd.exe):

    ```bash
    set DOCKER_BUILDKIT=1 && docker build -t dspec2test .
    ```

**Step B: Start the environment:**

```bash
docker run --rm -it dspec2test
```

You are now inside the container at `/app`. The `dafny` binary is on PATH. All subsequent commands should be run in this terminal.

### 3. Smoke Test

To verify the artifact is functional, we will run the tool's core command on a simple correct program and a simple buggy program. This should take less than 5 minutes.

**Step A: Verify binary path**

- Run: 

```bash
dafny --version
```

- **Expected output**:

```bash
4.11.0
```


**Step B: Correct Program Demo**

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

- Run: 

```bash
dafny generate-tests Spec /app/Example/Example1.dfy --bva
```

> **Note**: By default, `generate-tests` prints to the console. For the tests to be printed onto a file, add `> /app/Example/Example1Tests.dfy` to the previous command.


- **Expected output** (test methods generated on stdout):

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

**Step C: Buggy Program Demo**

The file is pre-loaded in the image at `/app/Example/Example2.dfy`:

```dafny
method MatchFirst(s1: seq<int>, s2: seq<int>) returns (isMatch: bool)
  ensures isMatch == (|s1| == 0 || |s2| == 0 || s1[0] == s2[0])
{
  return |s1| == 1 || |s2| == 0 || s1[0] == s2[0];
}
```

This program has a bug: the implementation uses `|s1| == 1` instead of `|s1| == 0`.

- Run:

```bash
dafny generate-tests Spec /app/Example/Example2.dfy --bva
```

> **Note**: By default, `generate-tests` prints to the console. For the tests to be printed onto a file, add `> /app/Example/Example2Tests.dfy` to the previous command.


- **Expected output** (generates failing tests that expose the bug):

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

---

## Part II: Step-by-step Instructions

### 1. Paper Claims Supported by this Artifact

- **Claim 1** (Table 1 - Top): DSpec2Test (`Spec_bva`) achieves a higher mutation kill rate (93.9%) compared to the Block strategy (82.4%) on realistically killable mutants.

- **Claim 2** (Table 1 - Bottom): DSpec2Test covers unique mutants that the Block strategy fails to kill, showing a union kill rate of 95.4%.

### 2. Paper Claims NOT Supported by this Artifact

- **Execution Time / Performance**: Due to hardware variations across reviewer machines (and Docker overhead), precise execution times for test generation are not claimed or evaluated by this artifact.

### 3. Reproducing the Evaluation (Cached Results)

The evaluation uses mutation testing to measure test-generation effectiveness. To quickly view the raw automated results without regenerating mutants:

```bash
cd /app/Evaluation
python -m src.runners.run_evaluation --strategies=all
```

This runs the pipeline across all strategies (`Spec`, `Block`, `Spec_bva`) using cached data and outputs the raw metrics to the terminal and to results/comparison.json.

**Expected output:**
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

**Manual Analysis (Post-Evaluation)**

After running the regular evaluation pipeline, a **manual analysis** is required to produce
the final corrected results used in the paper. The raw kill rates include noise from:

1. **Incompetent mutants** — don't compile (resolution/type errors). Both tools report these as "killed" (non-zero exit from build failure).
2. **Equivalent mutants** — semantically identical to the original. No test can distinguish them.
3. **Timeouts** — all confirmed to be runtime infinite loops (loop-guard mutations on monotonic
   counters). These are reclassified as kills.

The manual classification for each of the 170 common mutants (`Block` a∩d `Spec_bva` scope) is stored in:

```
results/manually_analysis.json
```

To produce the final corrected results table (Table 1 in the paper):

```bash
cd Evaluation
python results_after_manual_analysis.py
```

**Expected output:**

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
Killed by Spec_bva only    —     —      17      —   13.0%
Killed by neither          —     —       6      —    4.6%

Denominator (realistically-killable): 131
Excluded: 22 incompetent + 17 equivalent = 39 (from 170 common mutants)
```

## 4. Reproducing the Evaluation (From Scratch)

If you wish to run the full pipeline from scratch (requires ~1 to 2.5 hours depending on your CPU):

**Step A: Generate Mutants (Approx. 30 mins)**

```bash
cd Evaluation
python -m src.runners.generate_mutants
```

**Step B:Run Evaluation (Approx. 1-2 hours)**

```bash
cd Evaluation
python -m src.runners.run_evaluation --strategies=all --clean-cache
```

**Step C: Apply Manual Analysis for Final Results**

```bash
python results_after_manual_analysis.py
```


## 5. Advanced Tool Documentation

You can run DSpec2Test manually on any .dfy file. It is advised to use the --length-limit X flag to keep generated sequences/sets reasonable.

```bash
dafny generate-tests Spec <file.dfy> --bva > OutputTests.dfy
```

**Available Flags:**

- `--bva`: Adds Boundary Value Analysis to test generation. Only works in `Spec` mode. Not compatible with the `--repeat` flag.

- `--simplify`: Simplifies test output by removing 'expect' statements related to pre/post conditions where possible, and instantiating the output with its actual value.

- `--fdnf`: Calculates the full DNF instead of safe DNF. Generates more clauses but drops short-circuit-safety guarantees.

- `--repeat N`: Repeats the pipeline N times to generate ~N times more tests. Default is 1.  Not compatible with the `--bva` flag.

- `--passing-failing`: Splits generated tests into passing and failing groups.


## 6. Artifact Layout

| Path | Contents |
| :--- | :--- |
| `/app/Binaries/Dafny` | DSpec2Test binary |
| `/app/Example/` | Demo programs (Example1.dfy, Example2.dfy) |
| `/app/Evaluation/dataset/selected_programs/` | 20 benchmark Dafny programs |
| `/app/Evaluation/dataset/selected_programs_mutants/` | Pre-generated mutants |
| `/app/Evaluation/results/` | Evaluation results (JSON) |
| `/app/Evaluation/src/` | Pipeline source code |

---