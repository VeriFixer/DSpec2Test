
method {:test} Test14() {
expect 7726 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7726 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := RectangleArea(7726, 7726);
expect r0 == 7726 * 7726;
}

// REPEAT 7 - TIME: 9.9973308 s