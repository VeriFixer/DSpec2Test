
method {:test} Test12() {
expect 62842 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62842);
expect r0 == Factorial(62842 % 10);
}

// REPEAT 7 - TIME: 10.8489414 s