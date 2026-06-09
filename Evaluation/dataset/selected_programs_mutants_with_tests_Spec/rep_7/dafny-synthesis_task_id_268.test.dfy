
method {:test} Test6() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(6);
expect r0 == 6 * 6 * (6 - 1) + 1;
}

// REPEAT 7 - TIME: 7.7647054 s