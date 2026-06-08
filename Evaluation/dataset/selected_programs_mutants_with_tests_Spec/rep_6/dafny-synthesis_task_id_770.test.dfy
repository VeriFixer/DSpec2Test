
method {:test} Test5() {
expect 63 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(63);
expect r0 == 63 * (2 * 63 + 1) * (24 * 63 * 63 * 63 - 12 * 63 * 63 - 14 * 63 + 7) / 15;
}

// REPEAT 6 - TIME: 20.3800483 s