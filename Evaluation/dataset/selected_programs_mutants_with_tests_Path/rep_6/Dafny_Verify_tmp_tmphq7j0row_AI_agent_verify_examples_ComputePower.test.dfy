
method {:test} Test5() {
expect 1803 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1803);
expect r0 == Power(1803);
}

// REPEAT 6 - TIME: 14.2063543 s