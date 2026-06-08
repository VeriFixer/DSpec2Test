
method {:test} Test6() {
expect 2486 > 0 && 14 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2486, 14);
expect r0 == (2486 + 14) / 2;
}

// REPEAT 7 - TIME: 8.4146401 s