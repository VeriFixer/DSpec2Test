
method {:test} Test12() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(106);
expect r0 == 106 * 106;
}

// REPEAT 7 - TIME: 10.7516437 s