
method {:test} Test9() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7721 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePyramidSurfaceArea(101, 7721);
expect r0 == 101 * 101 + 2 * 101 * 7721;
}

// REPEAT 2 - TIME: 6.6602367 s