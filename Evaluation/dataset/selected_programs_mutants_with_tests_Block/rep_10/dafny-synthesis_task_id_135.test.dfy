
method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(9);
expect r0 == 9 * (2 * 9 - 1);
}

// REPEAT 10 - TIME: 8.253387 s