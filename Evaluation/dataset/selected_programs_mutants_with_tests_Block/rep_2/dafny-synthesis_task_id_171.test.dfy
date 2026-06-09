
method {:test} Test1() {
expect 40 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(40);
expect r0 == 5 * 40;
}

// REPEAT 2 - TIME: 2.7221134 s