
method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(107);
expect r0 == 107 * (107 + 1) / 2;
}

// REPEAT 8 - TIME: 12.3620879 s