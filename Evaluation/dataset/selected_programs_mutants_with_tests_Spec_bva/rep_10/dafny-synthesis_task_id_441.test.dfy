
method {:test} Test14() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(109);
expect r0 == 6 * 109 * 109;
}

// REPEAT 10 - TIME: 10.5132325 s