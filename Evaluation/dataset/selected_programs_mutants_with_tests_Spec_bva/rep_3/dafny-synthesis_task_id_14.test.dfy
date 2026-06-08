
method {:test} Test12() {
expect 202 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 102 > 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 1425 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := TriangularPrismVolume(202, 102, 1425);
expect r0 == 202 * 102 * 1425 / 2;
}

// REPEAT 3 - TIME: 9.1344422 s