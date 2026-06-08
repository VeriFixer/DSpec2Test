
method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(105);
expect r0 == 105 * (2 * 105 - 1);
}

// REPEAT 6 - TIME: 10.0778859 s