
method {:test} Test5() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(6);
expect r0 == 6 * (6 + 1) / 2;
expect r1 == r0 as real / 6 as real;
}

// REPEAT 6 - TIME: 7.3298428 s