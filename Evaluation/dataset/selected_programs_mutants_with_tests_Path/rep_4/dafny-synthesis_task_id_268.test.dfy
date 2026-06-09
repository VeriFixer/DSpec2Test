
method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(3);
expect r0 == 6 * 3 * (3 - 1) + 1;
}

// REPEAT 4 - TIME: 6.2906946 s