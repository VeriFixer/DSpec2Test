
method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(103);
expect r0 == 103 * (103 + 1) * (103 + 2) / 6;
}

// REPEAT 4 - TIME: 7.6947601 s