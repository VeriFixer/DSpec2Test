
method {:test} Test11() {
expect 104.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 104.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(104.0, 104.0);
expect r0 == 3.14159265359 * 104.0 * 104.0 * 104.0;
}

// REPEAT 5 - TIME: 9.3351926 s