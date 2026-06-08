
method {:test} Test14() {
expect 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(109);
expect r0 == 109 * (109 + 1) * (109 + 2) / 6;
}

// REPEAT 10 - TIME: 11.9589534 s