
method {:test} Test16() {
expect 1 <= 10, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(10);
expect r0 == Factorial(10);
}

// REPEAT 9 - TIME: 10.3082964 s