
method {:test} Test2() {
expect 2478 > 0 && 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2478, 6);
expect r0 == (2478 + 6) / 2;
}

// REPEAT 3 - TIME: 4.2584153 s