
method {:test} Test1() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 == 1 || 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(2, 2);
expect 2 + r0 + r1 >= 2 * 2;
}

// REPEAT 2 - TIME: 10.3390614 s