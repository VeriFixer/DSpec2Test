
method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(9);
expect r0 == 9 * (7 * 9 - 5) / 2;
}

// REPEAT 10 - TIME: 9.8911537 s