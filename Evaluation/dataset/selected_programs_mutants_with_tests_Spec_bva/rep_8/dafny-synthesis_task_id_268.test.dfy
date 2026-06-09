
method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(107);
expect r0 == 6 * 107 * (107 - 1) + 1;
}

// REPEAT 8 - TIME: 9.6349562 s