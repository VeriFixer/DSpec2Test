
method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(105);
expect r0 == 4 * 105 * 105 - 3 * 105;
}

// REPEAT 6 - TIME: 9.7817424 s