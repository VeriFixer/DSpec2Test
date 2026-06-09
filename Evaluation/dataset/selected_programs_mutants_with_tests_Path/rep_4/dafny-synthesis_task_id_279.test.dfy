
method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := NthDecagonalNumber(3);
expect r0 == 4 * 3 * 3 - 3 * 3;
}

// REPEAT 4 - TIME: 7.7820158 s