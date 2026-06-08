
method {:test} Test3() {
expect 4.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 4.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(4.0, 4.0);
expect r0 == 3.14159265359 * 4.0 * 4.0 * 4.0;
}

// REPEAT 4 - TIME: 4.7091814 s