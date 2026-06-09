
method {:test} Test9() {
expect 2476 > 0 && 200 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2476, 200);
expect r0 == (2476 + 200) / 2;
}

// REPEAT 2 - TIME: 7.1127265 s