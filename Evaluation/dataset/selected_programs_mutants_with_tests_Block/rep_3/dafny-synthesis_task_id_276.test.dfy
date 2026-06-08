
method {:test} Test2() {
expect 3.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 3.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(3.0, 3.0);
expect r0 == 3.14159265359 * 3.0 * 3.0 * 3.0;
}

// REPEAT 3 - TIME: 3.7841752 s