
method {:test} Test8() {
expect 2490 > 0 && 18 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := MedianLength(2490, 18);
expect r0 == (2490 + 18) / 2;
}

// REPEAT 9 - TIME: 9.0074029 s