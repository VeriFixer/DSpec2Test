
method {:test} Test3() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 == 1 || 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(4, 4);
expect 4 + r0 + r1 >= 2 * 4;
}

// REPEAT 4 - TIME: 3.7599135 s