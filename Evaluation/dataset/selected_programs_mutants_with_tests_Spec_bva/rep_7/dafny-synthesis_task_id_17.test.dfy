
method {:test} Test11() {
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(106);
expect r0 == 4 * 106;
}

// REPEAT 7 - TIME: 9.1956578 s