
method {:test} Test8() {
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(103);
expect r0 + 1 == 103;
}

// REPEAT 3 - TIME: 6.1060454 s