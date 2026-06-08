
method {:test} Test15() {
expect 1 <= 109, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(109);
expect r0 == Factorial(109);
}

// REPEAT 10 - TIME: 13.5377215 s