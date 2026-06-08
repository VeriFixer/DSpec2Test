
method {:test} Test9() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(10);
expect r0 == 10 * (2 * 10 + 1) * (24 * 10 * 10 * 10 - 12 * 10 * 10 - 14 * 10 + 7) / 15;
}

// REPEAT 10 - TIME: 9.2286779 s