
method {:test} Test14() {
expect 2486 > 0 && 210 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2486, 210);
expect r0 == (2486 + 210) / 2;
}

// REPEAT 7 - TIME: 10.6997061 s