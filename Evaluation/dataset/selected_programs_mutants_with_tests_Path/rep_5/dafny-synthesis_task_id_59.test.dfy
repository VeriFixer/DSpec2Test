
method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(4);
expect r0 == 4 * (3 * 4 - 2);
}

// REPEAT 5 - TIME: 7.9744697 s