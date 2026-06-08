
method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(6);
expect r0 == 6 * (3 * 6 - 2);
}

// REPEAT 7 - TIME: 10.0473775 s