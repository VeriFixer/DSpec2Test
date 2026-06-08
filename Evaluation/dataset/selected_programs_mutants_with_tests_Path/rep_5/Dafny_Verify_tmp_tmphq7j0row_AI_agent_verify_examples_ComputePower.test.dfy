
method {:test} Test4() {
expect 1802 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1802);
expect r0 == Power(1802);
}

// REPEAT 5 - TIME: 19.6074206 s