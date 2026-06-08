
method {:test} Test1() {
expect 3 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(3, 2, 2);
expect r0 == 3 * 2 * 2 / 2;
}

// REPEAT 2 - TIME: 2.9424953 s