
method {:test} Test12() {
expect 105.0 > 0.0 && 105.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderLateralSurfaceArea(105.0, 105.0);
expect r0 == 2.0 * (105.0 * 105.0) * 3.14;
}

// REPEAT 6 - TIME: 10.9484858 s