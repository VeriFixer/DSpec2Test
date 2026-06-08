
method {:test} Test15() {
expect 7730 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7730);
expect r0 == Power(7730);
}

// REPEAT 10 - TIME: 12.0366985 s