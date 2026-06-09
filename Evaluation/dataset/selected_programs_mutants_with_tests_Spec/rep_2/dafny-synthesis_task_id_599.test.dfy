
method {:test} Test1() {
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(2);
expect r0 == 2 * (2 + 1) / 2;
expect r1 == r0 as real / 2 as real;
}

// REPEAT 2 - TIME: 3.3622894 s