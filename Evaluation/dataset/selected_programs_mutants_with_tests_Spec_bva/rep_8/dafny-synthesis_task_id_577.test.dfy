
method {:test} Test13() {
expect 62843 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62843);
expect r0 == Factorial(62843 % 10);
}

// REPEAT 8 - TIME: 11.4165406 s