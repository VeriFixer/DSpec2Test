
method {:test} Test8() {
expect 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(9.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 9.0 * 9.0 * 9.0;
}

// REPEAT 9 - TIME: 9.8160774 s