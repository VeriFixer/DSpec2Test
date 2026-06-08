
method {:test} Test15() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(109);
expect r0 == 109 * 109;
}

// REPEAT 10 - TIME: 12.5676847 s