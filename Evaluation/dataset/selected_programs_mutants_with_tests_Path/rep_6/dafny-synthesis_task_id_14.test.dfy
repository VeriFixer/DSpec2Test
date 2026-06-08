
method {:test} Test5() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(7, 6, 6);
expect r0 == 7 * 6 * 6 / 2;
}

// REPEAT 6 - TIME: 9.1776979 s