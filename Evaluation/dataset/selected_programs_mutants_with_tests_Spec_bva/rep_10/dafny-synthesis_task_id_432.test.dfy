
method {:test} Test17() {
expect 2491 > 0 && 215 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2491, 215);
expect r0 == (2491 + 215) / 2;
}

// REPEAT 10 - TIME: 11.9665656 s