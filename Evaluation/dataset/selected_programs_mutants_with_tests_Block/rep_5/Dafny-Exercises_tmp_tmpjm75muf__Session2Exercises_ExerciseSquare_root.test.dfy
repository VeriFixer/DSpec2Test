
method {:test} Test16() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(5);
expect r0 >= 0 && r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}
method {:test} Test17() {
expect 6 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(6);
expect r0 >= 0 && r0 * r0 <= 6 < (r0 + 1) * (r0 + 1);
}
method {:test} Test18() {
expect 624 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(624);
expect r0 >= 0 && r0 * r0 <= 624 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 10.1517578 s