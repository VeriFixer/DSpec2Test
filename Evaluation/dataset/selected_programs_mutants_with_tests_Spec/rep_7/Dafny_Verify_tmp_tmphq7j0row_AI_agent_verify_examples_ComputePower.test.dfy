
method {:test} Test6() {
expect 2445 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(2445);
expect r0 == Power(2445);
}

// REPEAT 7 - TIME: 8.9197679 s