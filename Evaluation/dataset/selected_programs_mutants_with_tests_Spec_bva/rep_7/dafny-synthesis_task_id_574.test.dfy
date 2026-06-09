
method {:test} Test13() {
expect 106.0 > 0.0 && 106.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(106.0, 106.0);
expect r0 == 2.0 * 3.14159265358979323846 * 106.0 * (106.0 + 106.0);
}

// REPEAT 7 - TIME: 9.7699863 s