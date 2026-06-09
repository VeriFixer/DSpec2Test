
method {:test} Test7() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(7);
expect r0 == 6 * 7 * (7 - 1) + 1;
}

// REPEAT 8 - TIME: 9.3749565 s