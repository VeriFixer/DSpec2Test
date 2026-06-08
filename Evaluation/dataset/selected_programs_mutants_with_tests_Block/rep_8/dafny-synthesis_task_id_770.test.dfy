
method {:test} Test7() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(8);
expect r0 == 8 * (2 * 8 + 1) * (24 * 8 * 8 * 8 - 12 * 8 * 8 - 14 * 8 + 7) / 15;
}

// REPEAT 8 - TIME: 7.6997123 s