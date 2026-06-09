
method {:test} Test6() {
expect 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(11);
expect r0 == 11 * (2 * 11 - 1) * (2 * 11 + 1) / 3;
}

// REPEAT 7 - TIME: 26.6174822 s