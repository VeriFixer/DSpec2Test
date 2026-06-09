
method {:test} Test7() {
expect 7725 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8 == 1 || 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7725, 8);
expect 8 + r0 + r1 >= 2 * 7725;
}

// REPEAT 7 - TIME: 9.3305151 s