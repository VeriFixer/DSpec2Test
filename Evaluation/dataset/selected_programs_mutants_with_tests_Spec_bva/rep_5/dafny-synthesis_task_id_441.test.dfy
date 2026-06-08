
method {:test} Test9() {
expect 104 > 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := CubeSurfaceArea(104);
expect r0 == 6 * 104 * 104;
}

// REPEAT 5 - TIME: 8.4724248 s