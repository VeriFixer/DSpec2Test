
method {:test} Test15() {
expect 24 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(24);
expect r0 >= 0 && r0 * r0 <= 24 < (r0 + 1) * (r0 + 1);
}
method {:test} Test16() {
expect 24 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(24);
expect r0 >= 0 && r0 * r0 <= 24 < (r0 + 1) * (r0 + 1);
}
method {:test} Test17() {
expect 24 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(24);
expect r0 >= 0 && r0 * r0 <= 24 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 11.813393 s