
method {:test} Test8() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1662 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(10, 9, 1662);
expect r0 == 10 * 9 * 1662 / 2;
}

// REPEAT 9 - TIME: 8.3179761 s