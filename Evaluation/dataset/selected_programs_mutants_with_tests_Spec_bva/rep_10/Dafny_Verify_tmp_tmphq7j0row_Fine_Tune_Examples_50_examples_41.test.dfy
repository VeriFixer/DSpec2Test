
method {:test} Test32() {
expect 7728 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 109 == 1 || 109 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7728, 109);
expect 109 + r0 + r1 >= 2 * 7728;
}

// REPEAT 10 - TIME: 14.2567954 s