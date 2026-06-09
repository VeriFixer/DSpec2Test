
method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(9);
expect r0 == 4 * 9 * 9;
}

// REPEAT 9 - TIME: 10.6386733 s