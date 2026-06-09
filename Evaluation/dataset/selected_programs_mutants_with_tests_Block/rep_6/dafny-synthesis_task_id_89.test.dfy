
method {:test} Test5() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(6);
expect r0 + 1 == 6;
}

// REPEAT 6 - TIME: 6.3337441 s