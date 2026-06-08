
method {:test} Test3() {
expect 4.0 > 0.0 && 4.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(4.0, 4.0);
expect r0 == 2.0 * 3.14159265358979323846 * 4.0 * (4.0 + 4.0);
}

// REPEAT 4 - TIME: 6.5830427 s