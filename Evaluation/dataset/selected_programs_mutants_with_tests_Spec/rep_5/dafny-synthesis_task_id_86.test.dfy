
method {:test} Test4() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(5);
expect r0 == 3 * 5 * (5 - 1) + 1;
}

// REPEAT 5 - TIME: 5.3993779 s