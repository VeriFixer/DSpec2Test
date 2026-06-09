
method {:test} Test5() {
expect 7 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1659 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(7, 6, 1659);
expect r0 == 7 * 6 * 1659 / 2;
}

// REPEAT 6 - TIME: 6.2397412 s