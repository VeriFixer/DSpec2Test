
method {:test} Test13() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(108);
expect r0 == 108 * (108 + 1) * (108 + 2) / 6;
}

// REPEAT 9 - TIME: 10.21207 s