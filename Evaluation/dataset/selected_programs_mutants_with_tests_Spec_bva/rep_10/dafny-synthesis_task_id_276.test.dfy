
method {:test} Test16() {
expect 109.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 109.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(109.0, 109.0);
expect r0 == 3.14159265359 * 109.0 * 109.0 * 109.0;
}

// REPEAT 10 - TIME: 12.990499 s