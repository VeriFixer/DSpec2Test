
method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(4);
expect r0 == 4 * (2 * 4 - 1);
}

// REPEAT 5 - TIME: 7.0762854 s