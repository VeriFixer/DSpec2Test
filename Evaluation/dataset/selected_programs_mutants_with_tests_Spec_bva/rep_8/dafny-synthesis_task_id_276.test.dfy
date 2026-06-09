
method {:test} Test14() {
expect 107.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 107.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(107.0, 107.0);
expect r0 == 3.14159265359 * 107.0 * 107.0 * 107.0;
}

// REPEAT 8 - TIME: 10.725096 s