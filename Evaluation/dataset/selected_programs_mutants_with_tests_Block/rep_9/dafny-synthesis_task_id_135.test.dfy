
method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(8);
expect r0 == 8 * (2 * 8 - 1);
}

// REPEAT 9 - TIME: 7.6361805 s