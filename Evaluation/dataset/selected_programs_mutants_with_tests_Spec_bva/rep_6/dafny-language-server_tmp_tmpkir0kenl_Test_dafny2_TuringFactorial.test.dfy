
method {:test} Test11() {
expect 1 <= 105, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(105);
expect r0 == Factorial(105);
}

// REPEAT 6 - TIME: 10.8560979 s