
method {:test} Test5() {
expect 1 <= 7, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(7);
expect r0 == Factorial(7);
}

// REPEAT 6 - TIME: 7.9280789 s