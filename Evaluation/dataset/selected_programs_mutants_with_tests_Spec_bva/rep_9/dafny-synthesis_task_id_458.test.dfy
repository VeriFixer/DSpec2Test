
method {:test} Test16() {
expect 7728 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7728 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7728, 7728);
expect r0 == 7728 * 7728;
}

// REPEAT 9 - TIME: 11.2360965 s