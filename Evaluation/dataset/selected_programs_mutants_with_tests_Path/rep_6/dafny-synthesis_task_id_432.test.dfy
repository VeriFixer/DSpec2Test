
method {:test} Test5() {
expect 7 > 0 && 2479 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(7, 2479);
expect r0 == (7 + 2479) / 2;
}

// REPEAT 6 - TIME: 9.3003882 s