
method {:test} Test2() {
expect 60 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(60);
expect r0 == 60 * (2 * 60 + 1) * (24 * 60 * 60 * 60 - 12 * 60 * 60 - 14 * 60 + 7) / 15;
}

// REPEAT 3 - TIME: 17.3001189 s