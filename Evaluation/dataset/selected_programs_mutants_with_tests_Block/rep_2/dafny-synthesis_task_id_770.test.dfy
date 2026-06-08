
method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(2);
expect r0 == 2 * (2 * 2 + 1) * (24 * 2 * 2 * 2 - 12 * 2 * 2 - 14 * 2 + 7) / 15;
}

// REPEAT 2 - TIME: 3.3471602 s