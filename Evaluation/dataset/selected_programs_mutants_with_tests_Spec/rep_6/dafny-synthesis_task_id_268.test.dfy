
method {:test} Test5() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(5);
expect r0 == 6 * 5 * (5 - 1) + 1;
}

// REPEAT 6 - TIME: 7.1769959 s