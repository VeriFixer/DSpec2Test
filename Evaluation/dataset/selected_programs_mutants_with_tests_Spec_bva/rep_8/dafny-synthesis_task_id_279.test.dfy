
method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(107);
expect r0 == 4 * 107 * 107 - 3 * 107;
}

// REPEAT 8 - TIME: 9.9948628 s