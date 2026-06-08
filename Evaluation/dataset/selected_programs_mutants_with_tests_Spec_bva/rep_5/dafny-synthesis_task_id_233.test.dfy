
method {:test} Test11() {
expect 104.0 > 0.0 && 104.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(104.0, 104.0);
expect r0 == 2.0 * (104.0 * 104.0) * 3.14;
}

// REPEAT 5 - TIME: 10.1230549 s