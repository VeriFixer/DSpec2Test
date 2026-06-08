
method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(9, 9);
expect r0 == 9 * 9;
}

// REPEAT 9 - TIME: 7.9595006 s