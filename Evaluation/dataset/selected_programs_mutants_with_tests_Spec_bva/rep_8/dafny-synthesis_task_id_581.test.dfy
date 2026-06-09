
method {:test} Test15() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7727 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(107, 7727);
expect r0 == 107 * 107 + 2 * 107 * 7727;
}

// REPEAT 8 - TIME: 10.6387358 s