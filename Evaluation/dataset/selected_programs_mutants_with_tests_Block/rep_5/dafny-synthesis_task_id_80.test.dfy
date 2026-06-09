
method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(4);
expect r0 == 4 * (4 + 1) * (4 + 2) / 6;
}

// REPEAT 5 - TIME: 4.9769148 s