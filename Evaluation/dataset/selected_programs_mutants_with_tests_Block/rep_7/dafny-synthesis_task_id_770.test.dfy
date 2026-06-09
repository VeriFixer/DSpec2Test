
method {:test} Test6() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(7);
expect r0 == 7 * (2 * 7 + 1) * (24 * 7 * 7 * 7 - 12 * 7 * 7 - 14 * 7 + 7) / 15;
}

// REPEAT 7 - TIME: 6.6816737 s