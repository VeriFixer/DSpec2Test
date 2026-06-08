
method {:test} Test14() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7726 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(106, 7726);
expect r0 == 106 * 106 + 2 * 106 * 7726;
}

// REPEAT 7 - TIME: 10.7719972 s