
method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(2);
expect r0 == 2 * (2 + 1) * (2 + 2) / 6;
}

// REPEAT 3 - TIME: 2.4320392 s