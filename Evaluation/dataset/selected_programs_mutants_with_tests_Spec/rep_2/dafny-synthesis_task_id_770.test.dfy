
method {:test} Test1() {
expect 26 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(26);
expect r0 == 26 * (2 * 26 + 1) * (24 * 26 * 26 * 26 - 12 * 26 * 26 - 14 * 26 + 7) / 15;
}

// REPEAT 2 - TIME: 5.4488117 s