
method {:test} Test5() {
expect 17 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(17);
expect r0 == 17 * (17 + 1) / 2;
expect r1 == r0 as real / 17 as real;
}

// REPEAT 6 - TIME: 22.6923471 s