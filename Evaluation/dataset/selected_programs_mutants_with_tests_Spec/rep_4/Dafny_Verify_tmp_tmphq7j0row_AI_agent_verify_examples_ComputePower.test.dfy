
method {:test} Test3() {
expect 2442 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2442);
expect r0 == Power(2442);
}

// REPEAT 4 - TIME: 5.5774589 s