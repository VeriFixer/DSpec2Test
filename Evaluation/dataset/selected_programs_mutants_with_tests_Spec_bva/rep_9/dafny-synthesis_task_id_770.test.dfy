
method {:test} Test11() {
expect 202 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(202);
expect r0 == 202 * (2 * 202 + 1) * (24 * 202 * 202 * 202 - 12 * 202 * 202 - 14 * 202 + 7) / 15;
}

// REPEAT 9 - TIME: 100.1766668 s