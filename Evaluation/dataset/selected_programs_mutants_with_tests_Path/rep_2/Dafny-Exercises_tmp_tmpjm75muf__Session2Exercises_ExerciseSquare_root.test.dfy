
method {:test} Test3() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(1);
expect r0 >= 0 && r0 * r0 <= 1 < (r0 + 1) * (r0 + 1);
}
method {:test} Test4() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(1);
expect r0 >= 0 && r0 * r0 <= 1 < (r0 + 1) * (r0 + 1);
}
method {:test} Test5() {
expect 1 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(1);
expect r0 >= 0 && r0 * r0 <= 1 < (r0 + 1) * (r0 + 1);
}

// REPEAT 2 - TIME: 44.2400042 s