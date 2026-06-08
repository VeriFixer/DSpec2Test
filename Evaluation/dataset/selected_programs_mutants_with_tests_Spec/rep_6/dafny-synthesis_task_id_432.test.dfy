
method {:test} Test5() {
expect 2484 > 0 && 12 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2484, 12);
expect r0 == (2484 + 12) / 2;
}

// REPEAT 6 - TIME: 7.7125151 s