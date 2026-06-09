
method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(103);
expect r0 == 103 * (2 * 103 - 1);
}

// REPEAT 4 - TIME: 6.8525947 s