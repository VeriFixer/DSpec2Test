
method {:test} Test7() {
expect 19 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(19);
expect r0 == 19 * (19 + 1) / 2;
expect r1 == r0 as real / 19 as real;
}

// REPEAT 8 - TIME: 29.5241752 s