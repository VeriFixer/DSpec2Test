
method {:test} Test7() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(102);
expect r0 == 6 * 102 * 102;
}

// REPEAT 3 - TIME: 6.0879363 s