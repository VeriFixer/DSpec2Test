
method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(106);
expect r0 == 4 * 106 * 106 - 3 * 106;
}

// REPEAT 7 - TIME: 10.3715246 s