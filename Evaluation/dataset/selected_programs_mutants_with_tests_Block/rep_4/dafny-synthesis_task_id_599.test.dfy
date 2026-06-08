
method {:test} Test3() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(10);
expect r0 == 10 * (10 + 1) / 2;
expect r1 == r0 as real / 10 as real;
}

// REPEAT 4 - TIME: 5.3289467 s