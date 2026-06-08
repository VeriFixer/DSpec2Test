
method {:test} Test8() {
expect 101.0 > 0.0 && 101.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(101.0, 101.0);
expect r0 == 2.0 * 3.14159265358979323846 * 101.0 * (101.0 + 101.0);
}

// REPEAT 2 - TIME: 6.8734374 s