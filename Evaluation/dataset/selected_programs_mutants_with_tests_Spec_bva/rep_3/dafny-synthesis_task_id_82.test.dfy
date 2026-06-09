
method {:test} Test7() {
expect 102.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(102.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 102.0 * 102.0 * 102.0;
}

// REPEAT 3 - TIME: 5.9663288 s