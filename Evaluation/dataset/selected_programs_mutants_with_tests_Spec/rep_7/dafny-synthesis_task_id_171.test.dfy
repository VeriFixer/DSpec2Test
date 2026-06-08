
method {:test} Test6() {
expect 45 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(45);
expect r0 == 5 * 45;
}

// REPEAT 7 - TIME: 8.0136897 s