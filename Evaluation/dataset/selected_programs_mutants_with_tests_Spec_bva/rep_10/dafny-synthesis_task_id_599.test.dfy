
method {:test} Test16() {
expect 208 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(208);
expect r0 == 208 * (208 + 1) / 2;
expect r1 == r0 as real / 208 as real;
}

// REPEAT 10 - TIME: 12.7202598 s