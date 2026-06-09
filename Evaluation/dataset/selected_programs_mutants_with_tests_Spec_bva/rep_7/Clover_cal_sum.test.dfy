
method {:test} Test11() {
expect 106 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(106);
expect r0 == 106 * (106 + 1) / 2;
}

// REPEAT 7 - TIME: 9.5761091 s