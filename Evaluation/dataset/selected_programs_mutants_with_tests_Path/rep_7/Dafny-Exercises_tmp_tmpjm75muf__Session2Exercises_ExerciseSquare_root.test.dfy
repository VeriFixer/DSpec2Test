
method {:test} Test18() {
expect 169 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(169);
expect r0 >= 0 && r0 * r0 <= 169 < (r0 + 1) * (r0 + 1);
}
method {:test} Test19() {
expect 64 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(64);
expect r0 >= 0 && r0 * r0 <= 64 < (r0 + 1) * (r0 + 1);
}
method {:test} Test20() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(6);
expect r0 >= 0 && r0 * r0 <= 6 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 158.8324321 s