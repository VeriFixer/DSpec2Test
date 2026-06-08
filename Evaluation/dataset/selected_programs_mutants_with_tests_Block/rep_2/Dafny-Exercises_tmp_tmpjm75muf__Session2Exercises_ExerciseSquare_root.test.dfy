
method {:test} Test4() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(2);
expect r0 >= 0 && r0 * r0 <= 2 < (r0 + 1) * (r0 + 1);
}
method {:test} Test5() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(3);
expect r0 >= 0 && r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}
method {:test} Test6() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(5);
expect r0 >= 0 && r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}
method {:test} Test7() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(8);
expect r0 >= 0 && r0 * r0 <= 8 < (r0 + 1) * (r0 + 1);
}

// REPEAT 2 - TIME: 4.8022022 s