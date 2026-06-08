
method {:test} Test8() {
expect 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(9.0, 9.0);
expect r0 == 3.14159265359 * 9.0 * 9.0 * 9.0;
}

// REPEAT 9 - TIME: 9.9092595 s