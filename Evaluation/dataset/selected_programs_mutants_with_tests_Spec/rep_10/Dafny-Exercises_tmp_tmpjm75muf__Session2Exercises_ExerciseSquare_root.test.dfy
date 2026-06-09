
method {:test} Test27() {
expect 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(48);
expect r0 >= 0 && r0 * r0 <= 48 < (r0 + 1) * (r0 + 1);
}
method {:test} Test28() {
expect 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(48);
expect r0 >= 0 && r0 * r0 <= 48 < (r0 + 1) * (r0 + 1);
}
method {:test} Test29() {
expect 48 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(48);
expect r0 >= 0 && r0 * r0 <= 48 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 10.7182293 s