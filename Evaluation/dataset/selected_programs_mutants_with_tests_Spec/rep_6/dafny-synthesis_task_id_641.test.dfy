
method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthNonagonalNumber(5);
expect r0 == 5 * (7 * 5 - 5) / 2;
}

// REPEAT 6 - TIME: 6.7984411 s