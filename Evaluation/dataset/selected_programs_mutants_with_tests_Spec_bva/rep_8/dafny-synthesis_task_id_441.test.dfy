
method {:test} Test12() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(107);
expect r0 == 6 * 107 * 107;
}

// REPEAT 8 - TIME: 10.7151728 s