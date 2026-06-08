
method {:test} Test4() {
expect 5 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(5);
expect r0 == 5 * 5 * 5;
}

// REPEAT 5 - TIME: 6.8081321 s