
method {:test} Test8() {
expect 200 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(200);
expect r0 == 200 * (200 + 1) / 2;
expect r1 == r0 as real / 200 as real;
}

// REPEAT 2 - TIME: 7.9854582 s