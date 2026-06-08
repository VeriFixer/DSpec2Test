
method {:test} Test10() {
expect 62838 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62838);
expect r0 == Factorial(62838 % 10);
}

// REPEAT 5 - TIME: 9.554286 s