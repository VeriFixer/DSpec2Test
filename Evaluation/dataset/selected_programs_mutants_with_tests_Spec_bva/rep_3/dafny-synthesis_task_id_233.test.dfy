
method {:test} Test9() {
expect 102.0 > 0.0 && 102.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(102.0, 102.0);
expect r0 == 2.0 * (102.0 * 102.0) * 3.14;
}

// REPEAT 3 - TIME: 8.2646175 s