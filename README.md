# Dafny generate-tests

Dafny's generate-tests command is an experimental feature that automatically generates tests for Dafny methods and/or functions tagged with the `{:testEntry}` label.

In Dafny's current implementation, there are 3 modes. In this fork, a forth one was added, in order to allow for the generation of tests based solely on the method's/function's specification. It is called: Spec.

## How to run the Spec mode

Given your usual Dafny file, you must flag with `{:testEntry}` all the methods/functions you wish to generate tests for.

This mode allows you to specify how many tests you wish to generate for each method/function, using the `--test-count` flag.

If your Dafny file has the name Example.dfy, you access this feature by running:

```
dafny generate-tests Spec Example.dfy --test-count 5
```

However, this outputs the tests into the command line. If you wish to save them to a file run, instead:

```
dafny generate-tests Spec Example.dfy --test-count 5 > ExampleTests.dfy
```

## Future Works

- Implement feature on arrays
- Disregard the need of the `{:testEntry}` label, by generating tests for every method/function that does not successfuly verify
- Automatically split tests between passing and non-passing