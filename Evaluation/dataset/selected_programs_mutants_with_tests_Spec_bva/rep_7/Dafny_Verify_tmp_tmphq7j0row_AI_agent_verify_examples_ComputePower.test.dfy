
method {:test} Test12() {
expect 7727 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7727);
expect r0 == Power(7727);
}

// REPEAT 7 - TIME: 9.7256791 s