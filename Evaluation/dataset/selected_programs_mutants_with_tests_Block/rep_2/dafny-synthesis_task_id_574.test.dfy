
method {:test} Test1() {
expect 2.0 > 0.0 && 2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(2.0, 2.0);
expect r0 == 2.0 * 3.14159265358979323846 * 2.0 * (2.0 + 2.0);
}

// REPEAT 2 - TIME: 2.8307693 s