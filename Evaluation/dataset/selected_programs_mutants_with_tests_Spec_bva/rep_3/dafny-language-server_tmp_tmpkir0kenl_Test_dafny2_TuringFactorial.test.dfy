
method {:test} Test8() {
expect 1 <= 102, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputeFactorial(102);
expect r0 == Factorial(102);
}

// REPEAT 3 - TIME: 8.5553288 s