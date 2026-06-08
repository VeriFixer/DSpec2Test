
method {:test} Test11() {
expect 7723 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7723 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7723, 7723);
expect r0 == 7723 * 7723;
}

// REPEAT 4 - TIME: 8.9027804 s