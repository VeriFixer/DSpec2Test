
method {:test} Test6() {
expect 7.0 > 0.0 && 7.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(7.0, 7.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 7.0 * 7.0 * 7.0;
}

// REPEAT 7 - TIME: 7.2578547 s