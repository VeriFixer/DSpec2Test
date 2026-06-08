
method {:test} Test9() {
expect 2448 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2448);
expect r0 == Power(2448);
}

// REPEAT 10 - TIME: 11.0636202 s