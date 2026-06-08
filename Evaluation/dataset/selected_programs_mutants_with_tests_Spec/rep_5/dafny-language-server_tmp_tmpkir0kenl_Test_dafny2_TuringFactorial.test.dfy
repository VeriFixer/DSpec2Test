
method {:test} Test4() {
expect 1 <= 6, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(6);
expect r0 == Factorial(6);
}

// REPEAT 5 - TIME: 6.9595153 s