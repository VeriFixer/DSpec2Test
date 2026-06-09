
method {:test} Test10() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := AreaOfLargestTriangleInSemicircle(104);
expect r0 == 104 * 104;
}

// REPEAT 5 - TIME: 8.3388718 s