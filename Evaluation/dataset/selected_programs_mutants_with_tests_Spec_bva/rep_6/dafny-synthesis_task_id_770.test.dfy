
method {:test} Test8() {
expect 199 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(199);
expect r0 == 199 * (2 * 199 + 1) * (24 * 199 * 199 * 199 - 12 * 199 * 199 - 14 * 199 + 7) / 15;
}

// REPEAT 6 - TIME: 98.580644 s