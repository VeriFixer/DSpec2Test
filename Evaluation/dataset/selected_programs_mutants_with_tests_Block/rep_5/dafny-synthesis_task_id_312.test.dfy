
method {:test} Test4() {
expect 5.0 > 0.0 && 5.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(5.0, 5.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 5.0 * 5.0 * 5.0;
}

// REPEAT 5 - TIME: 5.1538021 s