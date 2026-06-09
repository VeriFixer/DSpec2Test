
method {:test} Test9() {
expect 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
expect 10 == 1 || 10 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0, r1 := main(10, 10);
expect 10 + r0 + r1 >= 2 * 10;
}

// REPEAT 10 - TIME: 38.0710963 s