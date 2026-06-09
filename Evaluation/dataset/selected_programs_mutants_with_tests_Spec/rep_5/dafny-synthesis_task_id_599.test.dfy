
method {:test} Test4() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(5);
expect r0 == 5 * (5 + 1) / 2;
expect r1 == r0 as real / 5 as real;
}

// REPEAT 5 - TIME: 5.6201332 s