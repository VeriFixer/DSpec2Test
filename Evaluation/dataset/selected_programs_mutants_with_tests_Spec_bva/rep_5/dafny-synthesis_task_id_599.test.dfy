
method {:test} Test11() {
expect 203 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(203);
expect r0 == 203 * (203 + 1) / 2;
expect r1 == r0 as real / 203 as real;
}

// REPEAT 5 - TIME: 9.59169 s