
method {:test} Test19() {
expect 209 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 109 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1432 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(209, 109, 1432);
expect r0 == 209 * 109 * 1432 / 2;
}

// REPEAT 10 - TIME: 12.9612579 s