
method {:test} Test2() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(4);
expect r0 == 3 * 4 * (4 - 1) + 1;
}

// REPEAT 3 - TIME: 2.9557625 s