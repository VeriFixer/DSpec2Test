
method {:test} Test5() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(6);
expect r0 == 6 * (6 + 1) / 2;
}

// REPEAT 6 - TIME: 4.9970579 s