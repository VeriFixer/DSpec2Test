
method {:test} Test10() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7722 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(102, 7722);
expect r0 == 102 * 102 + 2 * 102 * 7722;
}

// REPEAT 3 - TIME: 7.338286 s