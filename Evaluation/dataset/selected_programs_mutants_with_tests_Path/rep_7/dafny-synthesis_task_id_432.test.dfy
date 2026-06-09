
method {:test} Test6() {
expect 8 > 0 && 2480 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(8, 2480);
expect r0 == (8 + 2480) / 2;
}

// REPEAT 7 - TIME: 3.5932044 s