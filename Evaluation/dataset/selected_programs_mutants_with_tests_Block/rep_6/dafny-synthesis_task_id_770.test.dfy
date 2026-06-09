
method {:test} Test5() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(6);
expect r0 == 6 * (2 * 6 + 1) * (24 * 6 * 6 * 6 - 12 * 6 * 6 - 14 * 6 + 7) / 15;
}

// REPEAT 6 - TIME: 6.0371522 s