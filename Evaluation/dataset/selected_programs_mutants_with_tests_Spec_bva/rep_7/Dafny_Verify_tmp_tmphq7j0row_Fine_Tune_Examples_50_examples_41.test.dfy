
method {:test} Test29() {
expect 7725 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 106 == 1 || 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7725, 106);
expect 106 + r0 + r1 >= 2 * 7725;
}

// REPEAT 7 - TIME: 15.6104215 s