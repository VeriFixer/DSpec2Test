
method {:test} Test12() {
expect 7724 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7724 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7724, 7724);
expect r0 == 7724 * 7724;
}

// REPEAT 5 - TIME: 8.8291005 s