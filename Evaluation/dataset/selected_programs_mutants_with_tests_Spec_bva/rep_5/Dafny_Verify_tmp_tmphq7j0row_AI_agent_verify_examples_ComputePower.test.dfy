
method {:test} Test10() {
expect 7725 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7725);
expect r0 == Power(7725);
}

// REPEAT 5 - TIME: 8.286102 s