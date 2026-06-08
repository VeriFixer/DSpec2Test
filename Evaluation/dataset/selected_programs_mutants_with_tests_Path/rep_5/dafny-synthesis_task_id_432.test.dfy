
method {:test} Test4() {
expect 6 > 0 && 2478 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(6, 2478);
expect r0 == (6 + 2478) / 2;
}

// REPEAT 5 - TIME: 8.2618448 s