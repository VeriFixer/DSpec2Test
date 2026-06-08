
method {:test} Test9() {
expect 10.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 10.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(10.0, 10.0);
expect r0 == 3.14159265359 * 10.0 * 10.0 * 10.0;
}

// REPEAT 10 - TIME: 9.7200385 s