
method {:test} Test9() {
expect 17 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(17);
expect r0 == Factorial(17 % 10);
}

// REPEAT 10 - TIME: 9.2593562 s