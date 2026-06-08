
method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(4);
expect r0 == 4 * 4 * 4 - 3 * 4;
}

// REPEAT 5 - TIME: 5.4549959 s