
method {:test} Test3() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(4);
expect r0 == Power(4);
}

// REPEAT 4 - TIME: 4.1407926 s