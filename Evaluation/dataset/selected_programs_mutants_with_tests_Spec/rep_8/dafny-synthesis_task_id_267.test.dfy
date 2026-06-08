
method {:test} Test7() {
expect 19 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(19);
expect r0 == 19 * (2 * 19 - 1) * (2 * 19 + 1) / 3;
}

// REPEAT 8 - TIME: 9.3327009 s