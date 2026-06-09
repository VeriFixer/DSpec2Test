
method {:test} Test1() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(8);
expect r0 == 8 * (8 + 1) / 2;
expect r1 == r0 as real / 8 as real;
}

// REPEAT 2 - TIME: 3.3796915 s