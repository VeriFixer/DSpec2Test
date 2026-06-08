
method {:test} Test11() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7723 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(103, 7723);
expect r0 == 103 * 103 + 2 * 103 * 7723;
}

// REPEAT 4 - TIME: 8.7507595 s