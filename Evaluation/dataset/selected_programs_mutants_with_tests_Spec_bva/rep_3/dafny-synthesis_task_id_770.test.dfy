
method {:test} Test5() {
expect 196 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(196);
expect r0 == 196 * (2 * 196 + 1) * (24 * 196 * 196 * 196 - 12 * 196 * 196 - 14 * 196 + 7) / 15;
}

// REPEAT 3 - TIME: 97.0449169 s