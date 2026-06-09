
method {:test} Test13() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(108);
expect r0 == 6 * 108 * 108;
}

// REPEAT 9 - TIME: 9.8980662 s