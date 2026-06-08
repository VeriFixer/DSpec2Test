
method {:test} Test8() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(8);
expect r0 == 6 * 8 * (8 - 1) + 1;
}

// REPEAT 9 - TIME: 10.8209669 s