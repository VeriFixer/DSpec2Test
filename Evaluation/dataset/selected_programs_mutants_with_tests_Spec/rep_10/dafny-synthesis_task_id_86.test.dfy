
method {:test} Test9() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(10);
expect r0 == 3 * 10 * (10 - 1) + 1;
}

// REPEAT 10 - TIME: 8.9069879 s