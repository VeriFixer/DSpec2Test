
method {:test} Test9() {
expect 200 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(200);
expect r0 == 200 * (2 * 200 + 1) * (24 * 200 * 200 * 200 - 12 * 200 * 200 - 14 * 200 + 7) / 15;
}

// REPEAT 7 - TIME: 100.0117292 s