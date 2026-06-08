
method {:test} Test12() {
expect 105.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 105.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(105.0, 105.0);
expect r0 == 3.14159265359 * 105.0 * 105.0 * 105.0;
}

// REPEAT 6 - TIME: 10.1319387 s