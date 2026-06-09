
method {:test} Test11() {
expect 201 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(201, 101, 101);
expect r0 == 201 * 101 * 101 / 2;
}

// REPEAT 2 - TIME: 7.3985365 s