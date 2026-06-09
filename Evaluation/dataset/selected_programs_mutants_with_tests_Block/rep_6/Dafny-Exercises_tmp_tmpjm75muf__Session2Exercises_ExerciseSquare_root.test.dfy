
method {:test} Test20() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(6);
expect r0 >= 0 && r0 * r0 <= 6 < (r0 + 1) * (r0 + 1);
}
method {:test} Test21() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(7);
expect r0 >= 0 && r0 * r0 <= 7 < (r0 + 1) * (r0 + 1);
}
method {:test} Test22() {
expect 675 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(675);
expect r0 >= 0 && r0 * r0 <= 675 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 11.5880563 s