
method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(101);
expect r0 == 4 * 101 * 101 - 3 * 101;
}

// REPEAT 2 - TIME: 5.3677593 s