
method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(1);
expect r0 == 1 * (2 * 1 - 1);
}

// REPEAT 2 - TIME: 4.2673802 s