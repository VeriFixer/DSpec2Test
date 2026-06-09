
method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(106);
expect r0 == 106 * (3 * 106 - 2);
}

// REPEAT 7 - TIME: 9.272831 s