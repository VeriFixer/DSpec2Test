
method {:test} Test7() {
expect 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(102);
expect r0 == 102 * (102 + 1) / 2;
}

// REPEAT 3 - TIME: 7.5471614 s