
method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(6);
expect r0 == 6 * (2 * 6 - 1);
}

// REPEAT 7 - TIME: 6.2452577 s