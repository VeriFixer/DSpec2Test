
method {:test} Test7() {
expect 8.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(8.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 8.0 * 8.0 * 8.0;
}

// REPEAT 8 - TIME: 5.6176758 s