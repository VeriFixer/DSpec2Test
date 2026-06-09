
method {:test} Test7() {
expect 7722 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ComputePower(7722);
expect r0 == Power(7722);
}

// REPEAT 2 - TIME: 6.2611753 s