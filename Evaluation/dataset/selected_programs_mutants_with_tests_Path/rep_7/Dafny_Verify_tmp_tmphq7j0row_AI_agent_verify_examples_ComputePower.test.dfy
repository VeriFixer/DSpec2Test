
method {:test} Test6() {
expect 1804 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1804);
expect r0 == Power(1804);
}

// REPEAT 7 - TIME: 16.3206452 s