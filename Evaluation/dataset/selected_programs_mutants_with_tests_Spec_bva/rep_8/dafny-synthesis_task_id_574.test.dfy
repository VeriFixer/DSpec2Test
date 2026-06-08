
method {:test} Test14() {
expect 107.0 > 0.0 && 107.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(107.0, 107.0);
expect r0 == 2.0 * 3.14159265358979323846 * 107.0 * (107.0 + 107.0);
}

// REPEAT 8 - TIME: 11.169392 s