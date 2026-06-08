
method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthOctagonalNumber(105);
expect r0 == 105 * (3 * 105 - 2);
}

// REPEAT 6 - TIME: 9.7778217 s