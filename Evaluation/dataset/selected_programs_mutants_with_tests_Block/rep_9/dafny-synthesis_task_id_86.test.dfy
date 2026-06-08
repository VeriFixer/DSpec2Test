
method {:test} Test8() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(10);
expect r0 == 3 * 10 * (10 - 1) + 1;
}

// REPEAT 9 - TIME: 7.87475 s