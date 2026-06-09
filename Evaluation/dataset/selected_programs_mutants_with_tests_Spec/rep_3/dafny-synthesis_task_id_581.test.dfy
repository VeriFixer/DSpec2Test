
method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(3, 3);
expect r0 == 3 * 3 + 2 * 3 * 3;
}

// REPEAT 3 - TIME: 4.0453405 s