
method {:test} Test7() {
expect 8.0 > 0.0 && 8.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(8.0, 8.0);
expect r0 == 2.0 * 3.14159265358979323846 * 8.0 * (8.0 + 8.0);
}

// REPEAT 8 - TIME: 7.0977701 s