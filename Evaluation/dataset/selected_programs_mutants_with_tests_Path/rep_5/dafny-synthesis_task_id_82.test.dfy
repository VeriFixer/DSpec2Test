
method {:test} Test4() {
expect 5.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(5.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 5.0 * 5.0 * 5.0;
}

// REPEAT 5 - TIME: 3.977091 s