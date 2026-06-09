
method {:test} Test7() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(101);
expect r0 == 101 * 101;
}

// REPEAT 2 - TIME: 6.0205392 s