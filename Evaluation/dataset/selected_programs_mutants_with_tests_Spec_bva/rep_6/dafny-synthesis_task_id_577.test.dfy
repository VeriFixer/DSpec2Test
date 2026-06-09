
method {:test} Test11() {
expect 62839 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62839);
expect r0 == Factorial(62839 % 10);
}

// REPEAT 6 - TIME: 8.7365148 s