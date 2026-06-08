
method {:test} Test13() {
expect 106.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 106.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(106.0, 106.0);
expect r0 == 3.14159265359 * 106.0 * 106.0 * 106.0;
}

// REPEAT 7 - TIME: 10.8896181 s