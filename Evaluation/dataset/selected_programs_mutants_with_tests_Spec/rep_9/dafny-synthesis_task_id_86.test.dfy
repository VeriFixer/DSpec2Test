
method {:test} Test8() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(9);
expect r0 == 3 * 9 * (9 - 1) + 1;
}

// REPEAT 9 - TIME: 8.2854795 s