
method {:test} Test3() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(4);
expect r0 == 4 * (2 * 4 + 1) * (24 * 4 * 4 * 4 - 12 * 4 * 4 - 14 * 4 + 7) / 15;
}

// REPEAT 4 - TIME: 4.6573262 s