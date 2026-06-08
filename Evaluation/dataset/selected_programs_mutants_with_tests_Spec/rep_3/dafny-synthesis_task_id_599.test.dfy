
method {:test} Test2() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(3);
expect r0 == 3 * (3 + 1) / 2;
expect r1 == r0 as real / 3 as real;
}

// REPEAT 3 - TIME: 4.6091032 s