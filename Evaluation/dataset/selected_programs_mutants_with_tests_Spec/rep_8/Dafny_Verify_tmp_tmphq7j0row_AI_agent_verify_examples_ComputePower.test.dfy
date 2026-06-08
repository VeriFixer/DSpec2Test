
method {:test} Test7() {
expect 2446 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2446);
expect r0 == Power(2446);
}

// REPEAT 8 - TIME: 9.7272097 s