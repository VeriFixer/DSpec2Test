
method {:test} Test21() {
expect 26 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(26);
expect r0 >= 0 && r0 * r0 <= 26 < (r0 + 1) * (r0 + 1);
}
method {:test} Test22() {
expect 26 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(26);
expect r0 >= 0 && r0 * r0 <= 26 < (r0 + 1) * (r0 + 1);
}
method {:test} Test23() {
expect 26 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(26);
expect r0 >= 0 && r0 * r0 <= 26 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 14.8963241 s