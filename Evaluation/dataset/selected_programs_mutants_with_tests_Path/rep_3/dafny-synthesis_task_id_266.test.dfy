
method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(3);
expect r0 == 4 * 3 * 3;
}

// REPEAT 3 - TIME: 5.3106702 s