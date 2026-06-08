
method {:test} Test6() {
expect 101 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(101);
expect r0 == 101 * (101 + 1) / 2;
}

// REPEAT 2 - TIME: 6.5753126 s