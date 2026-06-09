
method {:test} Test9() {
expect 21 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(21);
expect r0 == 21 * (21 + 1) / 2;
expect r1 == r0 as real / 21 as real;
}

// REPEAT 10 - TIME: 36.8261927 s