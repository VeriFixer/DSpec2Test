
method {:test} Test2() {
expect 4 > 0 && 2476 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(4, 2476);
expect r0 == (4 + 2476) / 2;
}

// REPEAT 3 - TIME: 1.9436878 s