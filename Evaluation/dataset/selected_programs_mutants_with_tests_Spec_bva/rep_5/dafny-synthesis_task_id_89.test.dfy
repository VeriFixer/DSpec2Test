
method {:test} Test10() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(105);
expect r0 + 1 == 105;
}

// REPEAT 5 - TIME: 7.329235 s