
method {:test} Test13() {
expect 7725 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7725 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7725, 7725);
expect r0 == 7725 * 7725;
}

// REPEAT 6 - TIME: 10.4062475 s