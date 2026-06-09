
method {:test} Test5() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(6);
expect r0 == 6 * 6;
}

// REPEAT 6 - TIME: 5.5154556 s