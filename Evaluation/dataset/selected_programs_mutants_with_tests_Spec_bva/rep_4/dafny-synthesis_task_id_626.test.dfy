
method {:test} Test9() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(103);
expect r0 == 103 * 103;
}

// REPEAT 4 - TIME: 7.608864 s