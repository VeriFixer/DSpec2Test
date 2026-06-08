
method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(7);
expect r0 == 7 * (7 + 1) * (7 + 2) / 6;
}

// REPEAT 8 - TIME: 9.921041 s