
method {:test} Test8() {
expect 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(9.0);
expect r0 == 4.0 * 3.14159265358979323846 * 9.0 * 9.0;
}

// REPEAT 9 - TIME: 8.5376998 s