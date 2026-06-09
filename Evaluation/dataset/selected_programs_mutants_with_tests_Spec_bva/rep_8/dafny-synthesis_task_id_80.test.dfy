
method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(107);
expect r0 == 107 * (107 + 1) * (107 + 2) / 6;
}

// REPEAT 8 - TIME: 9.6308118 s