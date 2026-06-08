
method {:test} Test3() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(4, 4);
expect r0 == 4 * 4;
}

// REPEAT 4 - TIME: 4.2030755 s