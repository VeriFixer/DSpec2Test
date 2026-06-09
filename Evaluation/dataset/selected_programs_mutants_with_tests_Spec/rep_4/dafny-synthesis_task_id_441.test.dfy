
method {:test} Test3() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(4);
expect r0 == 6 * 4 * 4;
}

// REPEAT 4 - TIME: 4.9632681 s