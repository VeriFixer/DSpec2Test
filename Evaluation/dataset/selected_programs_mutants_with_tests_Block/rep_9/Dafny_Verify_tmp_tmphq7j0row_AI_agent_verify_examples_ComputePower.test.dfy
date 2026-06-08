
method {:test} Test8() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(9);
expect r0 == Power(9);
}

// REPEAT 9 - TIME: 7.6651384 s