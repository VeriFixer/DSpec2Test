# DSpec2Test — Extended Evaluation Guide (State-of-the-Art)

**⚠️ IMPORTANT DISCLAIMER FOR REVIEWERS ⚠️**
> This document and the associated extended evaluation are **NOT** required to validate the claims made in our accepted ASE paper. The paper's official results (evaluating 20 programs) are documented in the main [`README.md`](https://github.com/VeriFixer/DSpec2Test/blob/generate-tests/spec/README.md). 
>
> We are providing this extended evaluation (expanded to 200 programs) to demonstrate our ongoing work, recent bug fixes, and the improved robustness of DSpec2Test since the paper's acceptance.
>
> This evaluation additionally compares `Spec` and `SpecBva` to `Path` (previously the comparison was only done with `Block`)

---

## 1. Prerequisites and Setup

To run this extended evaluation, you must use the latest codebase.

> **Prerequisite:** Docker must be installed on your system. See the [official Docker installation guide](https://docs.docker.com/get-docker/) for instructions.

**Step A: Load the pre-built image:**

Ensure Docker is installed and running, then load the provided archive:

```bash
docker load -i dspec2test-extended.tar.gz
```

**[Optional]** If you wish to build the image from scratch, it takes ~10–20 mins (Z3 compiles from source) and requires ≥ 8GB RAM:

```bash
# 1. Clone the repository
git clone git@github.com:VeriFixer/DSpec2Test.git dspec2test-extended
cd dspec2test-extended

# 2. Pull submodules
git submodule update --init --recursive

# 3. Build the image (Takes ~10–20 mins, requires ≥8GB RAM)
DOCKER_BUILDKIT=1 docker build -t dspec2test-extended .
```

**Step B: Start the environment:**

```bash
docker run --rm -it dspec2test-extended
```

You are now inside the container at `/app`. The `dafny` binary is on PATH. All subsequent commands should be run in this terminal, executed from within the `Evaluation` directory:

```bash
cd /app/Evaluation
```

## 2. Quick View: Cached Results (Fast Path)
The Docker image comes pre-loaded with the cached results of this 10+ hour evaluation. If you want to instantly view the final outputs without running the full pipeline from scratch, simply run the evaluation command before generating new datasets or mutants:

```bash
python -m src.runners.run_evaluation 
```

Because the cache is fully populated, this will bypass test generation and execution, immediately printing the final evaluation metrics to your terminal, like this:

```bash
[2026-07-04 11:40:54,200] INFO __main__: Started at: 2026-07-04 11:40:54.200410
[run_evaluation] 214 originals, 2085 mutants

[run_evaluation] Strategy: Block
[run_evaluation] Cache hit for Block, loading from /app/Evaluation/results/results_Block

[run_evaluation] Strategy: Path
[run_evaluation] Cache hit for Path, loading from /app/Evaluation/results/results_Path

[run_evaluation] Strategy: Spec
[run_evaluation] Cache hit for Spec, loading from /app/Evaluation/results/results_Spec

[run_evaluation] Strategy: Spec_bva
[run_evaluation] Cache hit for Spec_bva, loading from /app/Evaluation/results/results_Spec_bva
Strategy       | Kill Rate | Killed | Survived | Not-Supported Programs | Not-Supported Mutants
---------------+-----------+--------+----------+------------------------+----------------------
Block_rep_1    | 63.14%    | 1213   | 570      | 18                     | 164                  
Path_rep_1     | 56.57%    | 917    | 586      | 48                     | 464                  
Spec_rep_1     | 56.31%    | 1076   | 709      | 19                     | 174                  
Spec_bva_rep_1 | 78.44%    | 1397   | 235      | 32                     | 304                  
[run_evaluation] Comparison written to /app/Evaluation/results/comparison.json
[2026-07-04 11:40:54,306] INFO __main__: Total run_evaluation.py time: 0.0000 hours
[2026-07-04 11:40:54,306] INFO __main__: Finished at: 2026-07-04 11:40:54.306167
```


Once this finishes, you can safely skip to Step D below to generate the graphs and tables.

## 3. Step-by-Step Extended Evaluation

The pipeline follows a similar logical structure to the original evaluation but operates on a significantly larger dataset and uses automated reporting tools for the final outputs.

**Step A: Generate the Dataset**

First, you must select and generate the dataset of Dafny programs. The list of target programs is defined in a CSV file located in the `dataset/csv/` directory. These files contain the programs that achieved an X% mutation score in [MutDafny](https://github.com/MutDafny/mutdafny)'s evaluation, to restrict the dataset to programs with highly restrictive specifications. Lower values of X retrieve higher amounts of programs.

Run the following command, replacing <name_of_file.csv> with the desired dataset file (e.g., `90-mutation-score.csv`):

```bash
python -m src.runners.generate_dataset --file "90-mutation-score.csv"
```

**Step B: Generate Mutants**

Next, generate the mutation testing environment for the newly created dataset.

```bash
python -m src.runners.generate_mutants
```

> **Note**: Because the dataset is 10x larger than the original paper, this step will take proportionally longer.

**Step C: Run the Evaluation**

Execute the main mutation testing evaluation across the programs.

> **Note**: This evaluation is computationally heavy. For context, it takes 10+ hours to complete on an Apple MacBook Air M1 with 16GB RAM.

The caching system remains active. If the run is interrupted, restarting this command will resume from the latest cached results rather than starting over, unless the `--clear-cahce` option is set.

```bash
python -m src.runners.run_evaluation 
```

Through the `--strategies` flag, it is possible to choose a subset of the available strategies for test generation (`Block` and `Path`, from the original `generate-tests` command, and `Spec` and `SpecBva`, introduced by DSpec2Test).

The `--repeat` flag will set the repeat parameter for test generation. Although in the previous (accepted) version, it was not compatible with the `--bva` flag (that creates `SpecBva` mode), now it is.

**Step D: Generate Reports (Graphs & Tables)**

Unlike the original paper evaluation which required a manual analysis script to filter out noise, this extended pipeline includes automated reporting scripts to synthesize the massive amount of output data.

To generate visual graphs of the results:

```bash
python -m src.mt_eval.reporting.graphs
```

Generated graphs will be saved in the respective output directory (i.e., results/graphs/).

To generate summary tables:

```bash
python -m src.mt_eval.reporting.tables
```
Generated tables will be saved in the respective output directory (i.e., results/tables/).
