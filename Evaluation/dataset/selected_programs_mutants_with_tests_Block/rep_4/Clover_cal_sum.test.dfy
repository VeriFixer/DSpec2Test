
method {:test} Test3() {
expect 1800 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(1800);
expect r0 == 1800 * (1800 + 1) / 2;
}

// REPEAT 4 - TIME: 3.5005482 s