
method {:test} Test10() {
expect 105 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(105);
expect r0 == 105 * 105 * 105;
}

// REPEAT 6 - TIME: 9.7908852 s