
method {:test} Test2() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(9);
expect r0 == 9 * (9 + 1) / 2;
expect r1 == r0 as real / 9 as real;
}

// REPEAT 3 - TIME: 4.3072379 s