
method {:test} Test9() {
expect 48 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(48);
expect r0 == 5 * 48;
}

// REPEAT 10 - TIME: 7.6488668 s