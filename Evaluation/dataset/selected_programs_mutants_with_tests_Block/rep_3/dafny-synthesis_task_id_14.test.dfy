
method {:test} Test2() {
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(4, 3, 3);
expect r0 == 4 * 3 * 3 / 2;
}

// REPEAT 3 - TIME: 3.1546185 s