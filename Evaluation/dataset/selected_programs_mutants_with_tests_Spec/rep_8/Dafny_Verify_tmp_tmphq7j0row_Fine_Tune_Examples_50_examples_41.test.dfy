
method {:test} Test8() {
expect 7726 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 9 == 1 || 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7726, 9);
expect 9 + r0 + r1 >= 2 * 7726;
}

// REPEAT 8 - TIME: 10.0896625 s