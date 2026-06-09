
method {:test} Test10() {
expect 7728 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 11 == 1 || 11 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7728, 11);
expect 11 + r0 + r1 >= 2 * 7728;
}

// REPEAT 10 - TIME: 11.5939172 s