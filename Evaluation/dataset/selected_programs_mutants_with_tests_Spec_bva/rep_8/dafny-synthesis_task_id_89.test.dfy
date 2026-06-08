
method {:test} Test13() {
expect 108 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(108);
expect r0 + 1 == 108;
}

// REPEAT 8 - TIME: 10.8696031 s