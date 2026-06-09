
method {:test} Test7() {
expect 12 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(12);
expect r0 == 12 * (2 * 12 - 1) * (2 * 12 + 1) / 3;
}

// REPEAT 8 - TIME: 30.5057831 s