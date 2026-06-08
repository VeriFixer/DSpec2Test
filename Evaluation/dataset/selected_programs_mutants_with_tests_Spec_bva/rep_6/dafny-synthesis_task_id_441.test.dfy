
method {:test} Test10() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(105);
expect r0 == 6 * 105 * 105;
}

// REPEAT 6 - TIME: 9.3504938 s