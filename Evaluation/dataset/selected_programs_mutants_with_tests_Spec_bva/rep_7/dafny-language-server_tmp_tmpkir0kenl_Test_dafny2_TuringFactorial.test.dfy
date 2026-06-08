
method {:test} Test12() {
expect 1 <= 106, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(106);
expect r0 == Factorial(106);
}

// REPEAT 7 - TIME: 11.522599 s