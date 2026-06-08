
method {:test} Test9() {
expect 1 <= 11, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(11);
expect r0 == Factorial(11);
}

// REPEAT 10 - TIME: 82.0870527 s