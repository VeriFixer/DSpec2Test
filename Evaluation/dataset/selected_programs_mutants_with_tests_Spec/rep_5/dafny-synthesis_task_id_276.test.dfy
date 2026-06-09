
method {:test} Test4() {
expect 5.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 5.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(5.0, 5.0);
expect r0 == 3.14159265359 * 5.0 * 5.0 * 5.0;
}

// REPEAT 5 - TIME: 5.7716507 s