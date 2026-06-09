
method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(8);
expect r0 == 8 * (8 + 1) * (8 + 2) / 6;
}

// REPEAT 9 - TIME: 8.7054511 s