
method {:test} Test12() {
expect 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := Sum(107);
expect r0 == 107 * (107 + 1) / 2;
}

// REPEAT 8 - TIME: 11.2351438 s