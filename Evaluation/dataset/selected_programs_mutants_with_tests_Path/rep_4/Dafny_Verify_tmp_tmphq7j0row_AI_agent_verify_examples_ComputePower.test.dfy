
method {:test} Test3() {
expect 1801 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1801);
expect r0 == Power(1801);
}

// REPEAT 4 - TIME: 16.6761772 s