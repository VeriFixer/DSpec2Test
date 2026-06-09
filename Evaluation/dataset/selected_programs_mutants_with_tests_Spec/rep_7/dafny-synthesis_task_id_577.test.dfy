
method {:test} Test6() {
expect 14 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(14);
expect r0 == Factorial(14 % 10);
}

// REPEAT 7 - TIME: 7.2801603 s