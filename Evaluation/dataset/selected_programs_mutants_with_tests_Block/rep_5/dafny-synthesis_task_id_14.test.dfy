
method {:test} Test4() {
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(6, 5, 5);
expect r0 == 6 * 5 * 5 / 2;
}

// REPEAT 5 - TIME: 5.0116706 s