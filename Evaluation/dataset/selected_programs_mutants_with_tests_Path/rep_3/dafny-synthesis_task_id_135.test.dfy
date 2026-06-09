
method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthHexagonalNumber(2);
expect r0 == 2 * (2 * 2 - 1);
}

// REPEAT 3 - TIME: 4.9780773 s