
method {:test} Test2() {
expect 2441 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2441);
expect r0 == Power(2441);
}

// REPEAT 3 - TIME: 5.1558918 s