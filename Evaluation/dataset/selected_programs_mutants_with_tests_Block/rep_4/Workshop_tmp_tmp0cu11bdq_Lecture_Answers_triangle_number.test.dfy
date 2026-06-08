
method {:test} Test3() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(4);
expect r0 == 4 * (4 + 1) / 2;
}

// REPEAT 4 - TIME: 4.53868 s