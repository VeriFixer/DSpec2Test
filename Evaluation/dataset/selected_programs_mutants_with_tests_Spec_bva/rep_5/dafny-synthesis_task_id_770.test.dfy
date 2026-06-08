
method {:test} Test7() {
expect 198 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(198);
expect r0 == 198 * (2 * 198 + 1) * (24 * 198 * 198 * 198 - 12 * 198 * 198 - 14 * 198 + 7) / 15;
}

// REPEAT 5 - TIME: 99.3432775 s