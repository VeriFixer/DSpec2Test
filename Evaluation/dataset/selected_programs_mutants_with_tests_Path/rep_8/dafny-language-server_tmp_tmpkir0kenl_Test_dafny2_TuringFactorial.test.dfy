
method {:test} Test7() {
expect 1 <= 9, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(9);
expect r0 == Factorial(9);
}

// REPEAT 8 - TIME: 63.5885772 s