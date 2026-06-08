
method {:test} Test9() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(10);
expect r0 == Power(10);
}

// REPEAT 10 - TIME: 8.2019886 s