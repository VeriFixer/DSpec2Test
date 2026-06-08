
method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(8);
expect r0 == 4 * 8 * 8 - 3 * 8;
}

// REPEAT 9 - TIME: 10.6109322 s