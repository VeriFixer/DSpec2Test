
method {:test} Test13() {
expect 106.0 > 0.0 && 106.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(106.0, 106.0);
expect r0 == 2.0 * (106.0 * 106.0) * 3.14;
}

// REPEAT 7 - TIME: 11.9600614 s