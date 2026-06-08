
method {:test} Test8() {
expect 9.0 > 0.0 && 9.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(9.0, 9.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 9.0 * 9.0 * 9.0;
}

// REPEAT 9 - TIME: 9.5258036 s