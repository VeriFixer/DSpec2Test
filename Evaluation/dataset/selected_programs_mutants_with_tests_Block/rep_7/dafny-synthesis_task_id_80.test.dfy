
method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(6);
expect r0 == 6 * (6 + 1) * (6 + 2) / 6;
}

// REPEAT 7 - TIME: 6.950683 s