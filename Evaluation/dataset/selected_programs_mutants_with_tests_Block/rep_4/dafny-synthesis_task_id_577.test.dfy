
method {:test} Test3() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(6);
expect r0 == Factorial(6 % 10);
}

// REPEAT 4 - TIME: 4.4381851 s