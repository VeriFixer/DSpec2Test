
method {:test} Test12() {
expect 203 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(203);
expect r0 == 203 * (2 * 203 + 1) * (24 * 203 * 203 * 203 - 12 * 203 * 203 - 14 * 203 + 7) / 15;
}

// REPEAT 10 - TIME: 101.109323 s