
method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(102);
expect r0 == 102 * (2 * 102 - 1);
}

// REPEAT 3 - TIME: 6.2677059 s