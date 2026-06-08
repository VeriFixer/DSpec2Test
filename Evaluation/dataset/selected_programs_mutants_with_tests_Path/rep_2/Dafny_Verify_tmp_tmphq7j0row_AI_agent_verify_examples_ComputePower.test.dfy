
method {:test} Test1() {
expect 1799 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1799);
expect r0 == Power(1799);
}

// REPEAT 2 - TIME: 10.3767223 s