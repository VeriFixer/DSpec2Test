
method {:test} Test8() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(102);
expect r0 == 102 * 102;
}

// REPEAT 3 - TIME: 7.8382518 s