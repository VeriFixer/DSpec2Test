
method {:test} Test8() {
expect 47 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := PentagonPerimeter(47);
expect r0 == 5 * 47;
}

// REPEAT 9 - TIME: 7.7746776 s