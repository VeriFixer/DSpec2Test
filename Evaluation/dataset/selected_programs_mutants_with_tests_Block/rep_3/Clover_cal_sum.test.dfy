
method {:test} Test2() {
expect 1799 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1799);
expect r0 == 1799 * (1799 + 1) / 2;
}

// REPEAT 3 - TIME: 2.9376942 s