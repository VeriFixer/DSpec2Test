
method {:test} Test4() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5 == 1 || 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(5, 5);
expect 5 + r0 + r1 >= 2 * 5;
}

// REPEAT 5 - TIME: 4.5966755 s