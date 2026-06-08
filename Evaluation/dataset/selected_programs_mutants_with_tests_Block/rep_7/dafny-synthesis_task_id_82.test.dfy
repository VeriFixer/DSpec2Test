
method {:test} Test6() {
expect 7.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(7.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 7.0 * 7.0 * 7.0;
}

// REPEAT 7 - TIME: 7.2241205 s