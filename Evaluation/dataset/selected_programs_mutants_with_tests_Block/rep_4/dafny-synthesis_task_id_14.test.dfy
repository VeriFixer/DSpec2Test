
method {:test} Test3() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(5, 4, 4);
expect r0 == 5 * 4 * 4 / 2;
}

// REPEAT 4 - TIME: 4.434682 s