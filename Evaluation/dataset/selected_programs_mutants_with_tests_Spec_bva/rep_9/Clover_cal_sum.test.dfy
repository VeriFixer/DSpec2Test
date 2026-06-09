
method {:test} Test13() {
expect 108 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(108);
expect r0 == 108 * (108 + 1) / 2;
}

// REPEAT 9 - TIME: 11.0927061 s