
method {:test} Test14() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(109);
expect r0 == 109 * (3 * 109 - 2);
}

// REPEAT 10 - TIME: 10.9541993 s