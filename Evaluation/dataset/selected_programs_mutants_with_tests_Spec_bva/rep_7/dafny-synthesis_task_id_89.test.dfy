
method {:test} Test12() {
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ClosestSmaller(107);
expect r0 + 1 == 107;
}

// REPEAT 7 - TIME: 10.2522861 s