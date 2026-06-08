
method {:test} Test15() {
expect 207 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(207);
expect r0 == 207 * (207 + 1) / 2;
expect r1 == r0 as real / 207 as real;
}

// REPEAT 9 - TIME: 13.2382328 s