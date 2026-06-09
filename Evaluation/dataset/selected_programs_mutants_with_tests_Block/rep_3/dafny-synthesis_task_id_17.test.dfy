
method {:test} Test2() {
expect 41 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SquarePerimeter(41);
expect r0 == 4 * 41;
}

// REPEAT 3 - TIME: 3.5837008 s