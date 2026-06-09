
method {:test} Test7() {
expect 1805 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(1805);
expect r0 == Power(1805);
}

// REPEAT 8 - TIME: 18.588376 s