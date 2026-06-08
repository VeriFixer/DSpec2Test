
method {:test} Test2() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(2);
expect r0 == 6 * 2 * (2 - 1) + 1;
}

// REPEAT 3 - TIME: 3.6175952 s