
method {:test} Test9() {
expect 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(11);
expect r0 == 3 * 11 * (11 - 1) + 1;
}

// REPEAT 10 - TIME: 8.1655198 s