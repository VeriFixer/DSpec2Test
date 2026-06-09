
method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(9);
expect r0 == 9 * (2 * 9 + 1) * (24 * 9 * 9 * 9 - 12 * 9 * 9 - 14 * 9 + 7) / 15;
}

// REPEAT 9 - TIME: 7.8527382 s