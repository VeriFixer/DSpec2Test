
method {:test} Test15() {
expect 62846 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62846);
expect r0 == Factorial(62846 % 10);
}

// REPEAT 10 - TIME: 11.3164773 s