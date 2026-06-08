
method {:test} Test5() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6 == 1 || 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(6, 6);
expect 6 + r0 + r1 >= 2 * 6;
}

// REPEAT 6 - TIME: 22.6501643 s