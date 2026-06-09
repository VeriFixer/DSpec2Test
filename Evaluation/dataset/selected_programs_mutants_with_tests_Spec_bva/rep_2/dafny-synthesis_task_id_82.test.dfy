
method {:test} Test6() {
expect 101.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(101.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 101.0 * 101.0 * 101.0;
}

// REPEAT 2 - TIME: 5.1706087 s