
method {:test} Test4() {
expect 14 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(14);
expect r0 == 14 * (14 + 1) / 2;
expect r1 == r0 as real / 14 as real;
}

// REPEAT 5 - TIME: 19.1482872 s