
method {:test} Test1() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(4);
expect r0 == Factorial(4 % 10);
}

// REPEAT 2 - TIME: 2.9467451 s