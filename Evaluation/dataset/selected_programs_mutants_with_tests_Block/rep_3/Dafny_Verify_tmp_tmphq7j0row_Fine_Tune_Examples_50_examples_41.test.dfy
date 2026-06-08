
method {:test} Test2() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 == 1 || 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(3, 3);
expect 3 + r0 + r1 >= 2 * 3;
}

// REPEAT 3 - TIME: 3.1863818 s