
method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(3);
expect r0 == 6 * 3 * 3;
}

// REPEAT 3 - TIME: 4.0183389 s