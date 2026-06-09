
method {:test} Test9() {
expect 201 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := SumAndAverage(201);
expect r0 == 201 * (201 + 1) / 2;
expect r1 == r0 as real / 201 as real;
}

// REPEAT 3 - TIME: 8.3571618 s