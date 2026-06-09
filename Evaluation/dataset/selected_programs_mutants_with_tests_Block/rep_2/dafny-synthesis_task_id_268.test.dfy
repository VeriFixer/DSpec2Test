
method {:test} Test1() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(1);
expect r0 == 6 * 1 * (1 - 1) + 1;
}

// REPEAT 2 - TIME: 2.9273427 s