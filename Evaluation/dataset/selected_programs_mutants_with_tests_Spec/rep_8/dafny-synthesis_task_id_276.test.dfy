
method {:test} Test7() {
expect 8.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 8.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(8.0, 8.0);
expect r0 == 3.14159265359 * 8.0 * 8.0 * 8.0;
}

// REPEAT 8 - TIME: 8.0550483 s