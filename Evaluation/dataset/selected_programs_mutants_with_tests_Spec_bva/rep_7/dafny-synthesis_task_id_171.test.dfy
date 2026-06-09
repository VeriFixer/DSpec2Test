
method {:test} Test11() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(106);
expect r0 == 5 * 106;
}

// REPEAT 7 - TIME: 8.7432282 s