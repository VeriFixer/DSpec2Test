
method {:test} Test10() {
expect 7722 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7722 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7722, 7722);
expect r0 == 7722 * 7722;
}

// REPEAT 3 - TIME: 7.3608278 s