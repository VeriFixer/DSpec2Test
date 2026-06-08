
method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(6);
expect r0 == 4 * 6 * 6 - 3 * 6;
}

// REPEAT 7 - TIME: 6.7610036 s