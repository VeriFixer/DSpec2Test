
method {:test} Test1() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2);
expect r0 == Power(2);
}

// REPEAT 2 - TIME: 2.5528335 s