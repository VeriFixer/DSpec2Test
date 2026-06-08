
method {:test} Test12() {
expect 204 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(204);
expect r0 == 204 * (204 + 1) / 2;
expect r1 == r0 as real / 204 as real;
}

// REPEAT 6 - TIME: 10.9180152 s