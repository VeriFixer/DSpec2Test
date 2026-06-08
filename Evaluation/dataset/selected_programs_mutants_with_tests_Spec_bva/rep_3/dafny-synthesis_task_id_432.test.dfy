
method {:test} Test10() {
expect 2478 > 0 && 202 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2478, 202);
expect r0 == (2478 + 202) / 2;
}

// REPEAT 3 - TIME: 8.0990829 s