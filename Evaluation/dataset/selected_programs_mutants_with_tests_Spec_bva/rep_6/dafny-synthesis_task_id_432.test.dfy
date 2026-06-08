
method {:test} Test13() {
expect 2484 > 0 && 208 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2484, 208);
expect r0 == (2484 + 208) / 2;
}

// REPEAT 6 - TIME: 10.1133335 s