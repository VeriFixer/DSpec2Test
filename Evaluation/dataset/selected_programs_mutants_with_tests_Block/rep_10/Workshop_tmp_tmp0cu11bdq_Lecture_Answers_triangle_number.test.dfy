
method {:test} Test9() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(10);
expect r0 == 10 * (10 + 1) / 2;
}

// REPEAT 10 - TIME: 7.475553 s