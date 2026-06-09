
method {:test} Test8() {
expect 7723 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7723);
expect r0 == Power(7723);
}

// REPEAT 3 - TIME: 6.9094235 s