
method {:test} Test6() {
expect 101 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeVolume(101);
expect r0 == 101 * 101 * 101;
}

// REPEAT 2 - TIME: 7.1791187 s