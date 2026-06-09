
method {:test} Test6() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(7, 7);
expect r0 == 7 * 7 + 2 * 7 * 7;
}

// REPEAT 7 - TIME: 7.3391055 s