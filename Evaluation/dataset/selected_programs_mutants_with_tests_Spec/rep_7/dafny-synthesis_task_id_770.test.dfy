
method {:test} Test6() {
expect 64 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(64);
expect r0 == 64 * (2 * 64 + 1) * (24 * 64 * 64 * 64 - 12 * 64 * 64 - 14 * 64 + 7) / 15;
}

// REPEAT 7 - TIME: 21.1084748 s