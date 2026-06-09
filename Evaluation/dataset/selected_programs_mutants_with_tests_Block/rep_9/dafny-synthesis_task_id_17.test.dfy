
method {:test} Test8() {
expect 47 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(47);
expect r0 == 4 * 47;
}

// REPEAT 9 - TIME: 7.8627107 s