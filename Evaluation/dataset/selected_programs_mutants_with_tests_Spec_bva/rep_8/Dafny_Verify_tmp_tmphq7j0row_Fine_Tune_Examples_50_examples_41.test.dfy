
method {:test} Test30() {
expect 7726 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 107 == 1 || 107 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7726, 107);
expect 107 + r0 + r1 >= 2 * 7726;
}

// REPEAT 8 - TIME: 16.3204954 s