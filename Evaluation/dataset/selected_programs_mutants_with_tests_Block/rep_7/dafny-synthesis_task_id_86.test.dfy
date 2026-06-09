
method {:test} Test6() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(8);
expect r0 == 3 * 8 * (8 - 1) + 1;
}

// REPEAT 7 - TIME: 6.4850331 s