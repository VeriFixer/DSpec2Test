
method {:test} Test4() {
expect 43 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(43);
expect r0 == 5 * 43;
}

// REPEAT 5 - TIME: 5.6357427 s