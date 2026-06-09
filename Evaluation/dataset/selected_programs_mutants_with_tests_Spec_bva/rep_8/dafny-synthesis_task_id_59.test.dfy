
method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(107);
expect r0 == 107 * (3 * 107 - 2);
}

// REPEAT 8 - TIME: 9.8524255 s