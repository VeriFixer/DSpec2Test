
method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(104);
expect r0 == 104 * (2 * 104 - 1);
}

// REPEAT 5 - TIME: 9.1710527 s