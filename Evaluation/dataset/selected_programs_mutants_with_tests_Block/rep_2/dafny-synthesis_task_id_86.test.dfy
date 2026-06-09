
method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(1);
expect r0 == 3 * 1 * (1 - 1) + 1;
}

// REPEAT 2 - TIME: 3.0011185 s