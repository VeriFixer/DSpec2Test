
method {:test} Test1() {
expect 9.0/8.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(9.0/8.0, 2.0, 9.0/8.0);
expect r0 == 9.0/8.0 - 1.0 / (4.0 * 9.0/8.0);
}

// REPEAT 2 - TIME: 3.29134 s