
method {:test} Test25() {
expect 7721 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 102 == 1 || 102 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7721, 102);
expect 102 + r0 + r1 >= 2 * 7721;
}

// REPEAT 3 - TIME: 12.8427423 s