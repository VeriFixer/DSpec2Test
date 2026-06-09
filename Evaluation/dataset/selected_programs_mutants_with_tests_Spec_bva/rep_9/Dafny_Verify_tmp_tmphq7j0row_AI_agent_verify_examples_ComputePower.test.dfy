
method {:test} Test14() {
expect 7729 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7729);
expect r0 == Power(7729);
}

// REPEAT 9 - TIME: 11.0570317 s