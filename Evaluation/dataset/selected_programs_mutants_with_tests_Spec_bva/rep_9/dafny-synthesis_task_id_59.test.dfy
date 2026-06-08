
method {:test} Test13() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(108);
expect r0 == 108 * (3 * 108 - 2);
}

// REPEAT 9 - TIME: 11.6442703 s