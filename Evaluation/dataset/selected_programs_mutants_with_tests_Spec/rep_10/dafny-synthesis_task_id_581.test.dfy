
method {:test} Test9() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(10, 10);
expect r0 == 10 * 10 + 2 * 10 * 10;
}

// REPEAT 10 - TIME: 9.2396769 s