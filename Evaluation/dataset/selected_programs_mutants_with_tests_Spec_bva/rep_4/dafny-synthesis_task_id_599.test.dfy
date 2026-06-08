
method {:test} Test10() {
expect 202 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(202);
expect r0 == 202 * (202 + 1) / 2;
expect r1 == r0 as real / 202 as real;
}

// REPEAT 4 - TIME: 9.4418772 s