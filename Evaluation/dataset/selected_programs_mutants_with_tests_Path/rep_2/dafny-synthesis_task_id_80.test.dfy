
method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TetrahedralNumber(1);
expect r0 == 1 * (1 + 1) * (1 + 2) / 6;
}

// REPEAT 2 - TIME: 4.187024 s