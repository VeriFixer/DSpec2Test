
method {:test} Test9() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(10);
expect r0 == 6 * 10 * 10;
}

// REPEAT 10 - TIME: 9.087432 s