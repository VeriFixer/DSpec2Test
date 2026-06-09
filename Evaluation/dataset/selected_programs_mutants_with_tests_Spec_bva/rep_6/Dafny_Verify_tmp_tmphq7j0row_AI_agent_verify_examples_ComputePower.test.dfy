
method {:test} Test11() {
expect 7726 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7726);
expect r0 == Power(7726);
}

// REPEAT 6 - TIME: 8.9737525 s