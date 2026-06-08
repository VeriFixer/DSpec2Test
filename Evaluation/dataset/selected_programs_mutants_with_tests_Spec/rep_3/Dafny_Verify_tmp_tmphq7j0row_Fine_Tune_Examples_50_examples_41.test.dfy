
method {:test} Test3() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 == 1 || 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(2, 4);
expect 4 + r0 + r1 >= 2 * 2;
}

// REPEAT 3 - TIME: 4.2238778 s