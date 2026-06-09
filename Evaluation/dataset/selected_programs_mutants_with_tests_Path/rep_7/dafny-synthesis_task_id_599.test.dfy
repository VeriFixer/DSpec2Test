
method {:test} Test6() {
expect 18 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(18);
expect r0 == 18 * (18 + 1) / 2;
expect r1 == r0 as real / 18 as real;
}

// REPEAT 7 - TIME: 25.9726423 s