
method {:test} Test4() {
expect 2482 > 0 && 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2482, 10);
expect r0 == (2482 + 10) / 2;
}

// REPEAT 5 - TIME: 6.9239676 s