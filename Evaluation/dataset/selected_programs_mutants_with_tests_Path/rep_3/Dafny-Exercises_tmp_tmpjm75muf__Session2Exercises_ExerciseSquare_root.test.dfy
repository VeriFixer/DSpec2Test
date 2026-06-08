
method {:test} Test6() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(2);
expect r0 >= 0 && r0 * r0 <= 2 < (r0 + 1) * (r0 + 1);
}
method {:test} Test7() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(4);
expect r0 >= 0 && r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}
method {:test} Test8() {
expect 2 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(2);
expect r0 >= 0 && r0 * r0 <= 2 < (r0 + 1) * (r0 + 1);
}

// REPEAT 3 - TIME: 61.3461284 s