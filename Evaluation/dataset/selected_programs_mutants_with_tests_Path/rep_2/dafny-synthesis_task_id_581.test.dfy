
method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(2, 2);
expect r0 == 2 * 2 + 2 * 2 * 2;
}

// REPEAT 2 - TIME: 3.9901948 s