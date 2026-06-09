
method {:test} Test11() {
expect 106.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(106.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 106.0 * 106.0 * 106.0;
}

// REPEAT 7 - TIME: 8.9487199 s