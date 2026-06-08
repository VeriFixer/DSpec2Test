
method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangleNumber(104);
expect r0 == 104 * (104 + 1) / 2;
}

// REPEAT 5 - TIME: 9.7420682 s