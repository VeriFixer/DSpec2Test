
method {:test} Test6() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(7);
expect r0 == 7 * (7 + 1) / 2;
expect r1 == r0 as real / 7 as real;
}

// REPEAT 7 - TIME: 7.0009442 s