
method {:test} Test10() {
expect 103.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 103.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(103.0, 103.0);
expect r0 == 3.14159265359 * 103.0 * 103.0 * 103.0;
}

// REPEAT 4 - TIME: 8.4511138 s