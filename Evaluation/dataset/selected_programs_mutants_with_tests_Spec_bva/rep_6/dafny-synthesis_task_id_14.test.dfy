
method {:test} Test15() {
expect 205 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1428 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(205, 105, 1428);
expect r0 == 205 * 105 * 1428 / 2;
}

// REPEAT 6 - TIME: 10.3322722 s