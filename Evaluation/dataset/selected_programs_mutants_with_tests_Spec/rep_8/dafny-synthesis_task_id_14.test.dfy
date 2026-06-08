
method {:test} Test7() {
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1661 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(9, 8, 1661);
expect r0 == 9 * 8 * 1661 / 2;
}

// REPEAT 8 - TIME: 9.4935735 s