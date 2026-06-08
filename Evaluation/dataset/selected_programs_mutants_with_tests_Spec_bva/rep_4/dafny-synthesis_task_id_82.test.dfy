
method {:test} Test8() {
expect 103.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := SphereVolume(103.0);
expect r0 == 4.0 / 3.0 * 3.1415926535 * 103.0 * 103.0 * 103.0;
}

// REPEAT 4 - TIME: 7.3859656 s