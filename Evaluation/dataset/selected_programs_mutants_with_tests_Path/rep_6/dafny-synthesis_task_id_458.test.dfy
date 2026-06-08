
method {:test} Test5() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(6, 6);
expect r0 == 6 * 6;
}

// REPEAT 6 - TIME: 9.3767154 s