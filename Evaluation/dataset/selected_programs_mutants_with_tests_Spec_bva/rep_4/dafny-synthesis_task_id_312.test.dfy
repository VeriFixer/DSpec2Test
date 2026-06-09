
method {:test} Test10() {
expect 103.0 > 0.0 && 103.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(103.0, 103.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 103.0 * 103.0 * 103.0;
}

// REPEAT 4 - TIME: 7.966626 s