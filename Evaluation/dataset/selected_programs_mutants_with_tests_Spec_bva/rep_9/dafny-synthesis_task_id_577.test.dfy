
method {:test} Test14() {
expect 62845 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62845);
expect r0 == Factorial(62845 % 10);
}

// REPEAT 9 - TIME: 12.079801 s