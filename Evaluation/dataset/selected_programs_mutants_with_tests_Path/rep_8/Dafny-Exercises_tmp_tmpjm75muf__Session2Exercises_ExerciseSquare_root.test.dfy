
method {:test} Test21() {
expect 170 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(170);
expect r0 >= 0 && r0 * r0 <= 170 < (r0 + 1) * (r0 + 1);
}
method {:test} Test22() {
expect 65 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(65);
expect r0 >= 0 && r0 * r0 <= 65 < (r0 + 1) * (r0 + 1);
}
method {:test} Test23() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(7);
expect r0 >= 0 && r0 * r0 <= 7 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 182.2699035 s