
method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(105);
expect r0 == 105 * (2 * 105 - 1) * (2 * 105 + 1) / 3;
}

// REPEAT 6 - TIME: 9.3120013 s