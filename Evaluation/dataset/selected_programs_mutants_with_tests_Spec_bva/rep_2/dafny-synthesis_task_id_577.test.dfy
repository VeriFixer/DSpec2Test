
method {:test} Test7() {
expect 62835 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := FactorialOfLastDigit(62835);
expect r0 == Factorial(62835 % 10);
}

// REPEAT 2 - TIME: 5.7860399 s