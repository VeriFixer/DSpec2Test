
method {:test} Test5() {
expect 6.0 > 0.0 && 6.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(6.0, 6.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 6.0 * 6.0 * 6.0;
}

// REPEAT 6 - TIME: 7.3425194 s