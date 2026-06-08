
method {:test} Test8() {
expect 13 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(13);
expect r0 == Factorial(13 % 10);
}

// REPEAT 9 - TIME: 11.3519991 s