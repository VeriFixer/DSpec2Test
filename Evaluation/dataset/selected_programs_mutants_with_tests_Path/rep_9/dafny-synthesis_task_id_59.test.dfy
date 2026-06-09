
method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(8);
expect r0 == 8 * (3 * 8 - 2);
}

// REPEAT 9 - TIME: 10.7210077 s