
method {:test} Test7() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(8, 8);
expect r0 == 8 * 8 + 2 * 8 * 8;
}

// REPEAT 8 - TIME: 7.035177 s