# DSpec2Test

Dafny's generate-tests command is an experimental feature that automatically generates tests for Dafny methods and/or functions tagged with the `{:testEntry}` label.

In Dafny's current implementation, there are 3 modes. In this fork, a forth one was added (**Spec**), in order to allow for the generation of tests based solely on the method's/function's specification.
This new integrated tool is called: DSpec2Test.

This mode comes with 5 additional flags:

- `--simplify`: Simplifies test output by including only input and output values." +
  "In other words, removes 'expect' statements related to pre and post condition, whenever possible.");

- `--fdnf`: Calculates the full DNF, instead of the safe DNF (default). It produces all 2^N − 1 non-empty subsets of branch satisfaction. For A || B: branches A ∧ B, A ∧ !B, !A ∧ B.
  Generates more clauses (more test scenarios) but drops the short-circuit-safety guarantee: tests may evaluate guarded subexpressions where the guard is false, potentially causing runtime errors (e.g.: out-of-bounds, division by zero).

- `--bva`: Adds Boundary Value Analysis to test generation. Cannot be used simultaneously with `--repeat`.

- `--repeat`: Repeats the pipeline N times, in order to generate, approximately, N times more tests than the initial iteration. 1 (default) indicates no repetition. Cannot be used simultaneously with `--bva`.

- `--passing-failing`: Splits generated tests into passing and failing.


## How to run

Given a Dafny file with methods and/or functions, the **Spec** mode will attempt to generate tests for each of them that fails to verify.
Additionally, one can flag methods/functions with `{:testEntry}`, in order to oblige the tool to generate tests for them.

Assuming your Dafny file is Example.dfy, you access this feature by running the following command, followed by any flags:

```
dafny generate-tests Spec Example.dfy
```

However, this outputs the tests into the command line. If you wish to save them to a file run, instead:

```
dafny generate-tests Spec Example.dfy > ExampleTests.dfy
```

Lastly, it is advised to run DSpec2Test with the `--length-limit X` flag, so that the length of sequences, sets, and maps in the generated tests are limited to a reasonable value.  