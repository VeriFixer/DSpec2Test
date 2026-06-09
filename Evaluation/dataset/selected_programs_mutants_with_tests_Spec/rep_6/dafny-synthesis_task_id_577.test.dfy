
method {:test} Test5() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(9);
expect r0 == Factorial(9 % 10);
}

// REPEAT 6 - TIME: 6.6388293 s