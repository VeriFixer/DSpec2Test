
method {:test} Test14() {
expect 204 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1427 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(204, 104, 1427);
expect r0 == 204 * 104 * 1427 / 2;
}

// REPEAT 5 - TIME: 10.515261 s