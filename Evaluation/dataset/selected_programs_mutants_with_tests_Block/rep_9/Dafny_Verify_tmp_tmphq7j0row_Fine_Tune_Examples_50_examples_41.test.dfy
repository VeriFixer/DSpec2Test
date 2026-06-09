
method {:test} Test8() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9 == 1 || 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(9, 9);
expect 9 + r0 + r1 >= 2 * 9;
}

// REPEAT 9 - TIME: 7.044246 s