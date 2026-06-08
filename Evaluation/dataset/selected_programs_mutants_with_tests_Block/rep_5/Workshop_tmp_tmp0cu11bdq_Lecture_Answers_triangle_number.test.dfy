
method {:test} Test4() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(5);
expect r0 == 5 * (5 + 1) / 2;
}

// REPEAT 5 - TIME: 5.2903877 s