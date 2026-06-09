
method {:test} Test8() {
expect 16 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(16);
expect r0 == Factorial(16 % 10);
}

// REPEAT 9 - TIME: 8.6168036 s