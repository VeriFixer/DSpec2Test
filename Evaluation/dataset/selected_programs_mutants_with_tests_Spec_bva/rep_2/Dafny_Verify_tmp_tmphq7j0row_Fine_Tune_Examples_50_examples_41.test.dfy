
method {:test} Test24() {
expect 7720 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 101 == 1 || 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7720, 101);
expect 101 + r0 + r1 >= 2 * 7720;
}

// REPEAT 2 - TIME: 12.0194918 s