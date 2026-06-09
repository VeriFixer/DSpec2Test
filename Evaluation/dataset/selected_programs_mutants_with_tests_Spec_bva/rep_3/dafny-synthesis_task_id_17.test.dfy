
method {:test} Test7() {
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(102);
expect r0 == 4 * 102;
}

// REPEAT 3 - TIME: 6.5283907 s