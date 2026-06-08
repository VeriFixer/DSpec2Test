
method {:test} Test5() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(7);
expect r0 == 3 * 7 * (7 - 1) + 1;
}

// REPEAT 6 - TIME: 8.0968724 s