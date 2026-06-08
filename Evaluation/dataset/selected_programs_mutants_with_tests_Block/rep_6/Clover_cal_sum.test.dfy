
method {:test} Test5() {
expect 1802 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1802);
expect r0 == 1802 * (1802 + 1) / 2;
}

// REPEAT 6 - TIME: 4.809987 s