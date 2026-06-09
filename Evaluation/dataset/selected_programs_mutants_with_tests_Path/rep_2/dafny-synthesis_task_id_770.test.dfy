
method {:test} Test1() {
expect 58 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(58);
expect r0 == 58 * (2 * 58 + 1) * (24 * 58 * 58 * 58 - 12 * 58 * 58 - 14 * 58 + 7) / 15;
}

// REPEAT 2 - TIME: 7.5668907 s