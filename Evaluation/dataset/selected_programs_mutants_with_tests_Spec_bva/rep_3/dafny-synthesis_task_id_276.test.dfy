
method {:test} Test9() {
expect 102.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 102.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(102.0, 102.0);
expect r0 == 3.14159265359 * 102.0 * 102.0 * 102.0;
}

// REPEAT 3 - TIME: 7.643521 s