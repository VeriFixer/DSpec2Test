
method {:test} Test14() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(108);
expect r0 == 108 * 108;
}

// REPEAT 9 - TIME: 11.0323029 s