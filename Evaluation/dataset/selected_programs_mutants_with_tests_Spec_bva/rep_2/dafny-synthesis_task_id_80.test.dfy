
method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(101);
expect r0 == 101 * (101 + 1) * (101 + 2) / 6;
}

// REPEAT 2 - TIME: 5.6741518 s