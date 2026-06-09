
method {:test} Test10() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(105);
expect r0 == 5 * 105;
}

// REPEAT 6 - TIME: 8.1357239 s