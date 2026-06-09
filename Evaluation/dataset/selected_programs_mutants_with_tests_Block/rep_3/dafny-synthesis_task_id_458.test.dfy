
method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(3, 3);
expect r0 == 3 * 3;
}

// REPEAT 3 - TIME: 3.5331188 s