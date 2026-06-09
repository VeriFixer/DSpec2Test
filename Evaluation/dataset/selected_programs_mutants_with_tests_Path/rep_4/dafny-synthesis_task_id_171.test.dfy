
method {:test} Test3() {
expect 42 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(42);
expect r0 == 5 * 42;
}

// REPEAT 4 - TIME: 6.7302296 s