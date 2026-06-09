
method {:test} Test3() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(3);
expect r0 >= 0 && r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}
method {:test} Test4() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(3);
expect r0 >= 0 && r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}
method {:test} Test5() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(3);
expect r0 >= 0 && r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}

// REPEAT 2 - TIME: 4.5356895 s