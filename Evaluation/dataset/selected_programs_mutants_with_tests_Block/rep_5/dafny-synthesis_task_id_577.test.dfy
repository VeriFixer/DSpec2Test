
method {:test} Test4() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(7);
expect r0 == Factorial(7 % 10);
}

// REPEAT 5 - TIME: 5.1798476 s