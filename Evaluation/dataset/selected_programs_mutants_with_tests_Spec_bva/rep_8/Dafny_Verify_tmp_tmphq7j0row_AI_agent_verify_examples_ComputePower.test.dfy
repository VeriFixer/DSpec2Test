
method {:test} Test13() {
expect 7728 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7728);
expect r0 == Power(7728);
}

// REPEAT 8 - TIME: 10.3884085 s