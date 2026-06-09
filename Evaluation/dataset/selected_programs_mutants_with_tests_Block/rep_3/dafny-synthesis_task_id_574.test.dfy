
method {:test} Test2() {
expect 3.0 > 0.0 && 3.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(3.0, 3.0);
expect r0 == 2.0 * 3.14159265358979323846 * 3.0 * (3.0 + 3.0);
}

// REPEAT 3 - TIME: 3.475022 s