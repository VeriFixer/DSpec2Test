
method {:test} Test6() {
expect 197 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(197);
expect r0 == 197 * (2 * 197 + 1) * (24 * 197 * 197 * 197 - 12 * 197 * 197 - 14 * 197 + 7) / 15;
}

// REPEAT 4 - TIME: 97.5927848 s