
method {:test} Test9() {
expect 7724 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7724);
expect r0 == Power(7724);
}

// REPEAT 4 - TIME: 7.6721538 s