
method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(5);
expect r0 == 5 * (2 * 5 - 1);
}

// REPEAT 6 - TIME: 8.5835814 s