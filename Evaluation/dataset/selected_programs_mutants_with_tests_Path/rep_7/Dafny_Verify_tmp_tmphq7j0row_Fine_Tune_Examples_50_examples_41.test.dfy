
method {:test} Test6() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 7 == 1 || 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(7, 7);
expect 7 + r0 + r1 >= 2 * 7;
}

// REPEAT 7 - TIME: 27.3574361 s