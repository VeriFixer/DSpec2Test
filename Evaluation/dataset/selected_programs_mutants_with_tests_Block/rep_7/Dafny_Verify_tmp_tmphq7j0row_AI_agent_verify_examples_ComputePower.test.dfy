
method {:test} Test6() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7);
expect r0 == Power(7);
}

// REPEAT 7 - TIME: 5.9180112 s