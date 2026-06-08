
method {:test} Test13() {
expect 1 <= 107, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(107);
expect r0 == Factorial(107);
}

// REPEAT 8 - TIME: 12.2329298 s