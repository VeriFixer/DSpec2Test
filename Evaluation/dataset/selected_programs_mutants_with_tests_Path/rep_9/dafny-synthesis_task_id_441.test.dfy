
method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(9);
expect r0 == 6 * 9 * 9;
}

// REPEAT 9 - TIME: 4.5659691 s