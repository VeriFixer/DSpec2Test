
method {:test} Test18() {
expect 25 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(25);
expect r0 >= 0 && r0 * r0 <= 25 < (r0 + 1) * (r0 + 1);
}
method {:test} Test19() {
expect 25 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(25);
expect r0 >= 0 && r0 * r0 <= 25 < (r0 + 1) * (r0 + 1);
}
method {:test} Test20() {
expect 25 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(25);
expect r0 >= 0 && r0 * r0 <= 25 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 13.3464694 s