
method {:test} Test8() {
expect 101.0 > 0.0 && 101.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(101.0, 101.0);
expect r0 == 2.0 * (101.0 * 101.0) * 3.14;
}

// REPEAT 2 - TIME: 7.3324893 s