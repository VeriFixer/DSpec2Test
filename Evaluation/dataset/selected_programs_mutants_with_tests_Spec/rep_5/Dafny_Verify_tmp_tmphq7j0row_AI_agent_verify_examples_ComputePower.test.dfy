
method {:test} Test4() {
expect 2443 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2443);
expect r0 == Power(2443);
}

// REPEAT 5 - TIME: 7.0406392 s