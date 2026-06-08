
method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(106);
expect r0 == 3 * 106 * (106 - 1) + 1;
}

// REPEAT 7 - TIME: 9.7980005 s