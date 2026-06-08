
method {:test} Test4() {
expect 5.0 > 0.0 && 5.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(5.0, 5.0);
expect r0 == 2.0 * 3.14159265358979323846 * 5.0 * (5.0 + 5.0);
}

// REPEAT 5 - TIME: 6.3589654 s