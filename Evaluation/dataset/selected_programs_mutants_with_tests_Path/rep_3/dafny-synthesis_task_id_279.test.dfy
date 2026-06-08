
method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(2);
expect r0 == 4 * 2 * 2 - 3 * 2;
}

// REPEAT 3 - TIME: 5.3641796 s