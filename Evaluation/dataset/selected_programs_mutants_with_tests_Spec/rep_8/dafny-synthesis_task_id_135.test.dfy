
method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(7);
expect r0 == 7 * (2 * 7 - 1);
}

// REPEAT 8 - TIME: 8.8643308 s