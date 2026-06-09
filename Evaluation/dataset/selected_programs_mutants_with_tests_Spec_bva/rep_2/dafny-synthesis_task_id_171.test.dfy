
method {:test} Test6() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(101);
expect r0 == 5 * 101;
}

// REPEAT 2 - TIME: 5.1061348 s