
method {:test} Test5() {
expect 2444 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2444);
expect r0 == Power(2444);
}

// REPEAT 6 - TIME: 8.0159813 s