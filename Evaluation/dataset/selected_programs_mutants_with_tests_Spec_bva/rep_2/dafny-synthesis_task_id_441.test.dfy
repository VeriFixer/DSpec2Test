
method {:test} Test6() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(101);
expect r0 == 6 * 101 * 101;
}

// REPEAT 2 - TIME: 5.9817602 s