
method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(5);
expect r0 == 5 * (3 * 5 - 2);
}

// REPEAT 6 - TIME: 6.3949101 s