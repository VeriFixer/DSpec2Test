
method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CenteredHexagonalNumber(104);
expect r0 == 3 * 104 * (104 - 1) + 1;
}

// REPEAT 5 - TIME: 8.496422 s