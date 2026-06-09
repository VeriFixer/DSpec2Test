
method {:test} Test2() {
expect 1800 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1800);
expect r0 == Power(1800);
}

// REPEAT 3 - TIME: 8.569934 s