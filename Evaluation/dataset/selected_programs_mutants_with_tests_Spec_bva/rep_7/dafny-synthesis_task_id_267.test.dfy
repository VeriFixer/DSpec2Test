
method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(106);
expect r0 == 106 * (2 * 106 - 1) * (2 * 106 + 1) / 3;
}

// REPEAT 7 - TIME: 10.025514 s