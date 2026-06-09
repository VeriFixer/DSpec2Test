
method {:test} Test1() {
expect 2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
expect 2.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CylinderVolume(2.0, 2.0);
expect r0 == 3.14159265359 * 2.0 * 2.0 * 2.0;
}

// REPEAT 2 - TIME: 4.2456818 s