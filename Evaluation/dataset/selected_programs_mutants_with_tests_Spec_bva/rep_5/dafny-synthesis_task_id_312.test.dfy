
method {:test} Test11() {
expect 104.0 > 0.0 && 104.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(104.0, 104.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 104.0 * 104.0 * 104.0;
}

// REPEAT 5 - TIME: 9.8002475 s