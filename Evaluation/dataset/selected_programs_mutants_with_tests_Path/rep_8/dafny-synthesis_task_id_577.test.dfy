
method {:test} Test7() {
expect 12 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(12);
expect r0 == Factorial(12 % 10);
}

// REPEAT 8 - TIME: 10.2465625 s