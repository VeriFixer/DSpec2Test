
method {:test} Test8() {
expect 20 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(20);
expect r0 == 20 * (20 + 1) / 2;
expect r1 == r0 as real / 20 as real;
}

// REPEAT 9 - TIME: 10.3449896 s