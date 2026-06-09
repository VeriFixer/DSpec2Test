
method {:test} Test3() {
expect 4.0 > 0.0 && 4.0 > 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ConeVolume(4.0, 4.0);
expect r0 == 1.0 / 3.0 * 3.14159265358979323846 * 4.0 * 4.0 * 4.0;
}

// REPEAT 4 - TIME: 4.4248015 s