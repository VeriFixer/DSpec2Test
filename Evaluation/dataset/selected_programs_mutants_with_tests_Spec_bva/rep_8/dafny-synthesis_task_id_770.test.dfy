
method {:test} Test10() {
expect 201 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SumOfFourthPowerOfOddNumbers(201);
expect r0 == 201 * (2 * 201 + 1) * (24 * 201 * 201 * 201 - 12 * 201 * 201 - 14 * 201 + 7) / 15;
}

// REPEAT 8 - TIME: 100.3350207 s