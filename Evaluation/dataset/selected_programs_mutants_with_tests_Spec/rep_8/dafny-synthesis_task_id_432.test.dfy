
method {:test} Test7() {
expect 2488 > 0 && 16 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2488, 16);
expect r0 == (2488 + 16) / 2;
}

// REPEAT 8 - TIME: 9.0921243 s