
method {:test} Test5() {
expect 6.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(6.0, 6.0);
expect r0 == 3.14159265359 * 6.0 * 6.0 * 6.0;
}

// REPEAT 6 - TIME: 6.7312748 s