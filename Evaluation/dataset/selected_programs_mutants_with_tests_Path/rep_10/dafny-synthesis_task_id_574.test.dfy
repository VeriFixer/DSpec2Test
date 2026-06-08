
method {:test} Test9() {
expect 10.0 > 0.0 && 10.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(10.0, 10.0);
expect r0 == 2.0 * 3.14159265358979323846 * 10.0 * (10.0 + 10.0);
}

// REPEAT 10 - TIME: 12.5670474 s