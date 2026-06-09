
method {:test} Test9() {
expect 11 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5930 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(11, 10, 5930);
expect r0 == 11 * 10 * 5930 / 2;
}

// REPEAT 10 - TIME: 7.3495677 s