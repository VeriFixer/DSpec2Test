
method {:test} Test15() {
expect 108.0 > 0.0 && 108.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(108.0, 108.0);
expect r0 == 2.0 * 3.14159265358979323846 * 108.0 * (108.0 + 108.0);
}

// REPEAT 9 - TIME: 11.7660824 s