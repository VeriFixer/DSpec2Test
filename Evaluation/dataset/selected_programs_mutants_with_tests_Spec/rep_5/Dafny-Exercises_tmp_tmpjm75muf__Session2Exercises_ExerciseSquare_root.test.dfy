
method {:test} Test12() {
expect 15 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(15);
expect r0 >= 0 && r0 * r0 <= 15 < (r0 + 1) * (r0 + 1);
}
method {:test} Test13() {
expect 15 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(15);
expect r0 >= 0 && r0 * r0 <= 15 < (r0 + 1) * (r0 + 1);
}
method {:test} Test14() {
expect 15 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(15);
expect r0 >= 0 && r0 * r0 <= 15 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 8.1436932 s