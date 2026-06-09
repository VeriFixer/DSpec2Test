
method {:test} Test9() {
expect 102.0 > 0.0 && 102.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(102.0, 102.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 102.0 * 102.0 * 102.0;
}

// REPEAT 3 - TIME: 7.1327593 s