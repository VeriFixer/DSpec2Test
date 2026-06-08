
method {:test} Test7() {
expect 65 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(65);
expect r0 == 65 * (2 * 65 + 1) * (24 * 65 * 65 * 65 - 12 * 65 * 65 - 14 * 65 + 7) / 15;
}

// REPEAT 9 - TIME: 52.0711887 s