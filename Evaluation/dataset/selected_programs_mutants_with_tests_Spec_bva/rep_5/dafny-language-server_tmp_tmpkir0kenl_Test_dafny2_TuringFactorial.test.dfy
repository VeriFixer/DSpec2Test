
method {:test} Test10() {
expect 1 <= 104, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(104);
expect r0 == Factorial(104);
}

// REPEAT 5 - TIME: 8.4018491 s