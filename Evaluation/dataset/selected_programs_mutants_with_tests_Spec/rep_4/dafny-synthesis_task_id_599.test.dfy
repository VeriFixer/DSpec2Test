
method {:test} Test3() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(4);
expect r0 == 4 * (4 + 1) / 2;
expect r1 == r0 as real / 4 as real;
}

// REPEAT 4 - TIME: 5.5201277 s