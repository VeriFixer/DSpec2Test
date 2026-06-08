
method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(8);
expect r0 == 8 * (8 + 1) / 2;
}

// REPEAT 9 - TIME: 9.8830126 s