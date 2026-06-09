
method {:test} Test2() {
expect 41 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(41);
expect r0 == 5 * 41;
}

// REPEAT 3 - TIME: 5.6499062 s