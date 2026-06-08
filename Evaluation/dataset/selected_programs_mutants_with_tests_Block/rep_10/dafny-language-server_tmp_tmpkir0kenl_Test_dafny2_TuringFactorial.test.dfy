
method {:test} Test18() {
expect 1 <= 11, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(11);
expect r0 == Factorial(11);
}

// REPEAT 10 - TIME: 12.3274893 s