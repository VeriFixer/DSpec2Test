
method {:test} Test13() {
expect 203 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 103 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1426 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(203, 103, 1426);
expect r0 == 203 * 103 * 1426 / 2;
}

// REPEAT 4 - TIME: 8.8993577 s