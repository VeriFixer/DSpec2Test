
method {:test} Test4() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := StarNumber(4);
expect r0 == 6 * 4 * (4 - 1) + 1;
}

// REPEAT 5 - TIME: 4.8574457 s