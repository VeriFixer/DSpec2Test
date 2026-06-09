
method {:test} Test5() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(6);
expect r0 == 3 * 6 * (6 - 1) + 1;
}

// REPEAT 6 - TIME: 6.2520785 s