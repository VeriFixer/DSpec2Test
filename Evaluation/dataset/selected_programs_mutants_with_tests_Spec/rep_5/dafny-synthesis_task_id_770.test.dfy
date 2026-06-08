
method {:test} Test4() {
expect 62 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(62);
expect r0 == 62 * (2 * 62 + 1) * (24 * 62 * 62 * 62 - 12 * 62 * 62 - 14 * 62 + 7) / 15;
}

// REPEAT 5 - TIME: 19.579811 s