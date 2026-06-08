
method {:test} Test4() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(5);
expect r0 == 5 * (2 * 5 + 1) * (24 * 5 * 5 * 5 - 12 * 5 * 5 - 14 * 5 + 7) / 15;
}

// REPEAT 5 - TIME: 5.6473728 s