
method {:test} Test9() {
expect 10.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(10.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 10.0 * 10.0 * 10.0;
}

// REPEAT 10 - TIME: 9.2637622 s