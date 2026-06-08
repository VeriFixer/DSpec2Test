
method {:test} Test14() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(109);
expect r0 == 3 * 109 * (109 - 1) + 1;
}

// REPEAT 10 - TIME: 11.5701416 s