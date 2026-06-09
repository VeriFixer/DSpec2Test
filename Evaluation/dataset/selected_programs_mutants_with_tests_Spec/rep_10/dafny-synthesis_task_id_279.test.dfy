
method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(9);
expect r0 == 4 * 9 * 9 - 3 * 9;
}

// REPEAT 10 - TIME: 8.9786477 s