
method {:test} Test27() {
expect 7723 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 104 == 1 || 104 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7723, 104);
expect 104 + r0 + r1 >= 2 * 7723;
}

// REPEAT 5 - TIME: 14.204314 s