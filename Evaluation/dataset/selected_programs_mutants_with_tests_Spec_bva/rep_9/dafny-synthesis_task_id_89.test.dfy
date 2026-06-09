
method {:test} Test14() {
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(109);
expect r0 + 1 == 109;
}

// REPEAT 9 - TIME: 9.8917991 s