
method {:test} Test2() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(3);
expect r0 == Power(3);
}

// REPEAT 3 - TIME: 3.33639 s