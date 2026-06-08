
method {:test} Test31() {
expect 7727 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 108 == 1 || 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7727, 108);
expect 108 + r0 + r1 >= 2 * 7727;
}

// REPEAT 9 - TIME: 13.8175381 s