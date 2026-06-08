
method {:test} Test17() {
expect 207 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 107 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1430 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(207, 107, 1430);
expect r0 == 207 * 107 * 1430 / 2;
}

// REPEAT 8 - TIME: 12.5604797 s