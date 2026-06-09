
method {:test} Test15() {
expect 2488 > 0 && 212 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2488, 212);
expect r0 == (2488 + 212) / 2;
}

// REPEAT 8 - TIME: 10.9639927 s