
method {:test} Test13() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(108);
expect r0 == 6 * 108 * (108 - 1) + 1;
}

// REPEAT 9 - TIME: 10.1794811 s