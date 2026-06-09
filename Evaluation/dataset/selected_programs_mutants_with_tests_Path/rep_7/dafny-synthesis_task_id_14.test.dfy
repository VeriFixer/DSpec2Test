
method {:test} Test6() {
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(8, 7, 7);
expect r0 == 8 * 7 * 7 / 2;
}

// REPEAT 7 - TIME: 9.2225872 s