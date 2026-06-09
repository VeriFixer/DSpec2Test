
method {:test} Test9() {
expect 1 <= 103, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(103);
expect r0 == Factorial(103);
}

// REPEAT 4 - TIME: 7.7954976 s