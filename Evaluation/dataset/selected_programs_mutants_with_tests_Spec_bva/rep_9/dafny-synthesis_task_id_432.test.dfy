
method {:test} Test16() {
expect 2490 > 0 && 214 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2490, 214);
expect r0 == (2490 + 214) / 2;
}

// REPEAT 9 - TIME: 11.5097565 s