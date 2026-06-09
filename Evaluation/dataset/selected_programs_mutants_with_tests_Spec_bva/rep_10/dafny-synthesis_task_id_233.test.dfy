
method {:test} Test16() {
expect 109.0 > 0.0 && 109.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(109.0, 109.0);
expect r0 == 2.0 * (109.0 * 109.0) * 3.14;
}

// REPEAT 10 - TIME: 11.4819628 s