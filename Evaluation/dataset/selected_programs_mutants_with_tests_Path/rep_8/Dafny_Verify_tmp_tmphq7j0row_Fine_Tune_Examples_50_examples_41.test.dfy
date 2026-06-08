
method {:test} Test7() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8 == 1 || 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(8, 8);
expect 8 + r0 + r1 >= 2 * 8;
}

// REPEAT 8 - TIME: 28.8745687 s