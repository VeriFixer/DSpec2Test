
method {:test} Test5() {
expect 17 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfSquaresOfFirstNOddNumbers(17);
expect r0 == 17 * (2 * 17 - 1) * (2 * 17 + 1) / 3;
}

// REPEAT 6 - TIME: 7.9320734 s