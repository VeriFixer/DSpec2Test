
method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(7);
expect r0 == 7 * (3 * 7 - 2);
}

// REPEAT 8 - TIME: 7.3032856 s