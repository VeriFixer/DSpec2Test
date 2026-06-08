
method {:test} Test9() {
expect 62837 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62837);
expect r0 == Factorial(62837 % 10);
}

// REPEAT 4 - TIME: 8.8465412 s