
method {:test} Test10() {
expect 105 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(105);
expect r0 == 105 * (105 + 1) / 2;
}

// REPEAT 6 - TIME: 8.9167395 s