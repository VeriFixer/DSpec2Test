
method {:test} Test14() {
expect 206 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(206);
expect r0 == 206 * (206 + 1) / 2;
expect r1 == r0 as real / 206 as real;
}

// REPEAT 8 - TIME: 12.3389672 s