
method {:test} Test15() {
expect 108.0 > 0.0 && 108.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(108.0, 108.0);
expect r0 == 2.0 * (108.0 * 108.0) * 3.14;
}

// REPEAT 9 - TIME: 10.8502995 s