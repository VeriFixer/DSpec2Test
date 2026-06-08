
method {:test} Test8() {
expect 1806 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1806);
expect r0 == Power(1806);
}

// REPEAT 9 - TIME: 33.548941 s