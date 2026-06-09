
method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(7);
expect r0 == 7 * (7 * 7 - 5) / 2;
}

// REPEAT 8 - TIME: 8.1735642 s