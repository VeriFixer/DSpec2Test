
method {:test} Test8() {
expect 62836 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62836);
expect r0 == Factorial(62836 % 10);
}

// REPEAT 3 - TIME: 6.577433 s