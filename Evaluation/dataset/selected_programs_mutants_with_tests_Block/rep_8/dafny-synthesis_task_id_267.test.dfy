
method {:test} Test7() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(8);
expect r0 == 8 * (2 * 8 - 1) * (2 * 8 + 1) / 3;
}

// REPEAT 8 - TIME: 7.3706281 s