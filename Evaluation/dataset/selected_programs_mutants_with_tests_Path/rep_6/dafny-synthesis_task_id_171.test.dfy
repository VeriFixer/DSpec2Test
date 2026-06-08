
method {:test} Test5() {
expect 44 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(44);
expect r0 == 5 * 44;
}

// REPEAT 6 - TIME: 8.6959698 s