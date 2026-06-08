
method {:test} Test7() {
expect 1 <= 101, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(101);
expect r0 == Factorial(101);
}

// REPEAT 2 - TIME: 7.4865792 s