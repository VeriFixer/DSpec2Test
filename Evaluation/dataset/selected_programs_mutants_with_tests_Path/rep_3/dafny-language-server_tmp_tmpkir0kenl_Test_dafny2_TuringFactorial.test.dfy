
method {:test} Test2() {
expect 1 <= 4, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(4);
expect r0 == Factorial(4);
}

// REPEAT 3 - TIME: 27.9675128 s