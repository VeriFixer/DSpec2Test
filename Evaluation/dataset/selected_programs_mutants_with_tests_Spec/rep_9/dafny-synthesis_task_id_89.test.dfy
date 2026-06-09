
method {:test} Test8() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(9);
expect r0 + 1 == 9;
}

// REPEAT 9 - TIME: 8.593573 s