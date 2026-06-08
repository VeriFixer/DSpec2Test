
method {:test} Test6() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := LateralSurfaceArea(101);
expect r0 == 4 * 101 * 101;
}

// REPEAT 2 - TIME: 6.6574554 s