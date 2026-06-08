
method {:test} Test1() {
expect 2.0 > 0.0 && 2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(2.0, 2.0);
expect r0 == 2.0 * (2.0 * 2.0) * 3.14;
}

// REPEAT 2 - TIME: 3.2878143 s