
method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(102);
expect r0 == 102 * (102 + 1) * (102 + 2) / 6;
}

// REPEAT 3 - TIME: 6.4254755 s