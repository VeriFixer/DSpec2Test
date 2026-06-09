
method {:test} Test9() {
expect 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(104);
expect r0 == 6 * 104 * (104 - 1) + 1;
}

// REPEAT 5 - TIME: 7.6274212 s