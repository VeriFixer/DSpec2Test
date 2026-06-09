
method {:test} Test8() {
expect 66 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(66);
expect r0 == 66 * (2 * 66 + 1) * (24 * 66 * 66 * 66 - 12 * 66 * 66 - 14 * 66 + 7) / 15;
}

// REPEAT 10 - TIME: 49.6702363 s