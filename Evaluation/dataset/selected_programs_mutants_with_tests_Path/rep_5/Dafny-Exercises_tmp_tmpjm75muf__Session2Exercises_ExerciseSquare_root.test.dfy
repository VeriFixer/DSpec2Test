
method {:test} Test12() {
expect 16 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(16);
expect r0 >= 0 && r0 * r0 <= 16 < (r0 + 1) * (r0 + 1);
}
method {:test} Test13() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(9);
expect r0 >= 0 && r0 * r0 <= 9 < (r0 + 1) * (r0 + 1);
}
method {:test} Test14() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(4);
expect r0 >= 0 && r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 94.9869008 s