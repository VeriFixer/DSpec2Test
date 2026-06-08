
method {:test} Test13() {
expect 205 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(205);
expect r0 == 205 * (205 + 1) / 2;
expect r1 == r0 as real / 205 as real;
}

// REPEAT 7 - TIME: 11.5841739 s