
method {:test} Test1() {
expect 2476 > 0 && 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2476, 4);
expect r0 == (2476 + 4) / 2;
}

// REPEAT 2 - TIME: 3.7221876 s