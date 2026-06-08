
method {:test} Test2() {
expect 1 <= 3, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(3);
expect r0 == Factorial(3);
}

// REPEAT 2 - TIME: 3.8036012 s