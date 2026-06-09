
method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(3);
expect r0 == 3 * (2 * 3 + 1) * (24 * 3 * 3 * 3 - 12 * 3 * 3 - 14 * 3 + 7) / 15;
}

// REPEAT 3 - TIME: 3.8817468 s