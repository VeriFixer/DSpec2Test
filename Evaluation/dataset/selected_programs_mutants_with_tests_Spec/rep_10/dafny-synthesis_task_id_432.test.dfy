
method {:test} Test9() {
expect 2492 > 0 && 20 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2492, 20);
expect r0 == (2492 + 20) / 2;
}

// REPEAT 10 - TIME: 9.6893594 s