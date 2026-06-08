
method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(4);
expect r0 == 4 * (7 * 4 - 5) / 2;
}

// REPEAT 5 - TIME: 6.319886 s