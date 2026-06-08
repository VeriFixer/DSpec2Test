
method {:test} Test10() {
expect 103.0 > 0.0 && 103.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderSurfaceArea(103.0, 103.0);
expect r0 == 2.0 * 3.14159265358979323846 * 103.0 * (103.0 + 103.0);
}

// REPEAT 4 - TIME: 8.479678 s