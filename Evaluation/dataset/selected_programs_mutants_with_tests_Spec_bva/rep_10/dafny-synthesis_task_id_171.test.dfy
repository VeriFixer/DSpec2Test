
method {:test} Test14() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(109);
expect r0 == 5 * 109;
}

// REPEAT 10 - TIME: 11.736407 s