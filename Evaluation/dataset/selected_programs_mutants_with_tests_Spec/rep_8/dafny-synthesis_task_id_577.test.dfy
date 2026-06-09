
method {:test} Test7() {
expect 15 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(15);
expect r0 == Factorial(15 % 10);
}

// REPEAT 8 - TIME: 7.957507 s