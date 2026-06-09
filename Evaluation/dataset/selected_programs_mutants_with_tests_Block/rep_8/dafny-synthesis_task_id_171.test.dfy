
method {:test} Test7() {
expect 46 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(46);
expect r0 == 5 * 46;
}

// REPEAT 8 - TIME: 6.4290706 s