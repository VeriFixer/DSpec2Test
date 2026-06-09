
method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(8);
expect r0 == 8 * (7 * 8 - 5) / 2;
}

// REPEAT 9 - TIME: 8.8743976 s