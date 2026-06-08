
method {:test} Test7() {
expect 8.0 > 0.0 && 8.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(8.0, 8.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 8.0 * 8.0 * 8.0;
}

// REPEAT 8 - TIME: 8.0490625 s