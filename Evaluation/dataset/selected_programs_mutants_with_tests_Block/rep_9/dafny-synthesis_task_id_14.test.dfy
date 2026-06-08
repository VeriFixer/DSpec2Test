
method {:test} Test8() {
expect 10 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5929 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(10, 9, 5929);
expect r0 == 10 * 9 * 5929 / 2;
}

// REPEAT 9 - TIME: 7.9006829 s