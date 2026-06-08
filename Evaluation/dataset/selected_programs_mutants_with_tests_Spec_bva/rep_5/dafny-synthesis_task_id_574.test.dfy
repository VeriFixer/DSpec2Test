
method {:test} Test11() {
expect 104.0 > 0.0 && 104.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(104.0, 104.0);
expect r0 == 2.0 * 3.14159265358979323846 * 104.0 * (104.0 + 104.0);
}

// REPEAT 5 - TIME: 9.2169605 s