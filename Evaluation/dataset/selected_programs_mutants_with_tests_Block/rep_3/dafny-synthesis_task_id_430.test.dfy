
method {:test} Test2() {
expect 89.0/72.0 != 0.0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := ParabolaDirectrix(89.0/72.0, 3.0, 89.0/72.0);
expect r0 == 89.0/72.0 - 1.0 / (4.0 * 89.0/72.0);
}

// REPEAT 3 - TIME: 3.6326692 s