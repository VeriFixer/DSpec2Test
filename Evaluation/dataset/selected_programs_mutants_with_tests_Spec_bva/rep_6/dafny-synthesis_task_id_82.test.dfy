
method {:test} Test10() {
expect 105.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(105.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 105.0 * 105.0 * 105.0;
}

// REPEAT 6 - TIME: 8.2371002 s