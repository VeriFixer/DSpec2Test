
method {:test} Test6() {
expect 7.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(7.0, 7.0);
expect r0 == 3.14159265359 * 7.0 * 7.0 * 7.0;
}

// REPEAT 7 - TIME: 7.3246125 s