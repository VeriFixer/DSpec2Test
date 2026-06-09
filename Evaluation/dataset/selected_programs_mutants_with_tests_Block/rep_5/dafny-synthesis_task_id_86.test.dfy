
method {:test} Test4() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(6);
expect r0 == 3 * 6 * (6 - 1) + 1;
}

// REPEAT 5 - TIME: 5.0508267 s