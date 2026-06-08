
method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(106);
expect r0 == 106 * (106 + 1) * (106 + 2) / 6;
}

// REPEAT 7 - TIME: 9.9692575 s