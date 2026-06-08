
method {:test} Test7() {
expect 9 > 0 && 2481 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(9, 2481);
expect r0 == (9 + 2481) / 2;
}

// REPEAT 8 - TIME: 7.601125 s