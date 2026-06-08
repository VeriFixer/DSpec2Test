
method {:test} Test12() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(4);
expect r0 >= 0 && r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}
method {:test} Test13() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(5);
expect r0 >= 0 && r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}
method {:test} Test14() {
expect 144 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(144);
expect r0 >= 0 && r0 * r0 <= 144 < (r0 + 1) * (r0 + 1);
}
method {:test} Test15() {
expect 576 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(576);
expect r0 >= 0 && r0 * r0 <= 576 < (r0 + 1) * (r0 + 1);
}

// REPEAT 4 - TIME: 8.6562301 s