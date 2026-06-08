
method {:test} Test14() {
expect 107.0 > 0.0 && 107.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(107.0, 107.0);
expect r0 == 2.0 * (107.0 * 107.0) * 3.14;
}

// REPEAT 8 - TIME: 12.7694958 s