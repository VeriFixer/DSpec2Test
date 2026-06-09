
method {:test} Test16() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7728 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(108, 7728);
expect r0 == 108 * 108 + 2 * 108 * 7728;
}

// REPEAT 9 - TIME: 11.4195264 s