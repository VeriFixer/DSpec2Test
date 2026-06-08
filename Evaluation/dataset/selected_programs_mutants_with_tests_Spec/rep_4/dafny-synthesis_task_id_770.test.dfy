
method {:test} Test3() {
expect 61 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(61);
expect r0 == 61 * (2 * 61 + 1) * (24 * 61 * 61 * 61 - 12 * 61 * 61 - 14 * 61 + 7) / 15;
}

// REPEAT 4 - TIME: 18.2487115 s