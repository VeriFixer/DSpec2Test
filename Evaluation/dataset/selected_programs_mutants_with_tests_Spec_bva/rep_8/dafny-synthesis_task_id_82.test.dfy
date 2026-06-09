
method {:test} Test12() {
expect 107.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(107.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 107.0 * 107.0 * 107.0;
}

// REPEAT 8 - TIME: 9.6751744 s