
method {:test} Test8() {
expect 10 > 0 && 2482 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(10, 2482);
expect r0 == (10 + 2482) / 2;
}

// REPEAT 9 - TIME: 8.0799272 s