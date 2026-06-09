
method {:test} Test9() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(9);
expect r0 == 9 * (9 + 1) * (9 + 2) / 6;
}

// REPEAT 10 - TIME: 9.2990104 s