
method {:test} Test7() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5928 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(9, 8, 5928);
expect r0 == 9 * 8 * 5928 / 2;
}

// REPEAT 8 - TIME: 6.3120638 s