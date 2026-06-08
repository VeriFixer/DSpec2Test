
method {:test} Test16() {
expect 206 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 106 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1429 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(206, 106, 1429);
expect r0 == 206 * 106 * 1429 / 2;
}

// REPEAT 7 - TIME: 11.858125 s