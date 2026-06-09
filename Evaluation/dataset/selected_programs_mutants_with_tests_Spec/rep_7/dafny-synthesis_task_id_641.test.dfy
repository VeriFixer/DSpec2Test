
method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(6);
expect r0 == 6 * (7 * 6 - 5) / 2;
}

// REPEAT 7 - TIME: 7.4354626 s