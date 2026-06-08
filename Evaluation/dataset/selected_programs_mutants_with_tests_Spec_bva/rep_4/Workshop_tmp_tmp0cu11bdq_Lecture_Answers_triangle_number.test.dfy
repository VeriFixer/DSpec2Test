
method {:test} Test8() {
expect 103 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(103);
expect r0 == 103 * (103 + 1) / 2;
}

// REPEAT 4 - TIME: 8.5603158 s