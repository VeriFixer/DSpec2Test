
method {:test} Test14() {
expect 1 <= 108, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(108);
expect r0 == Factorial(108);
}

// REPEAT 9 - TIME: 10.9071262 s