
method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(5);
expect r0 == 4 * 5 * 5 - 3 * 5;
}

// REPEAT 6 - TIME: 6.1495855 s