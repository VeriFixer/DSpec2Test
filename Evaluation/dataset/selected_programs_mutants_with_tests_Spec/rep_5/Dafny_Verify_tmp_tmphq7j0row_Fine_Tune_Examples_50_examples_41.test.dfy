
method {:test} Test5() {
expect 7723 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 6 == 1 || 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7723, 6);
expect 6 + r0 + r1 >= 2 * 7723;
}

// REPEAT 5 - TIME: 5.3214052 s