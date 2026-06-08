
method {:test} Test10() {
expect 105.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereSurfaceArea(105.0);
expect r0 == 4.0 * 3.14159265358979323846 * 105.0 * 105.0;
}

// REPEAT 6 - TIME: 8.9404399 s