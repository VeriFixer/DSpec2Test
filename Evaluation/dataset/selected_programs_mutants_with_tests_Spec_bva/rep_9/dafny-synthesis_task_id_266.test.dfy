
method {:test} Test13() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(108);
expect r0 == 4 * 108 * 108;
}

// REPEAT 9 - TIME: 11.1728293 s