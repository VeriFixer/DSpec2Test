
method {:test} Test6() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7, 7);
expect r0 == 7 * 7;
}

// REPEAT 7 - TIME: 5.2583994 s