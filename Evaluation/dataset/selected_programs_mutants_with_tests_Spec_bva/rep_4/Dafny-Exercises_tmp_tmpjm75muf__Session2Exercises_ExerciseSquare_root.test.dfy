
method {:test} Test30() {
expect 10403 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10403);
expect r0 >= 0 && r0 * r0 <= 10403 < (r0 + 1) * (r0 + 1);
}
method {:test} Test31() {
expect 10403 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10403);
expect r0 >= 0 && r0 * r0 <= 10403 < (r0 + 1) * (r0 + 1);
}
method {:test} Test32() {
expect 10403 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10403);
expect r0 >= 0 && r0 * r0 <= 10403 < (r0 + 1) * (r0 + 1);
}

// REPEAT 4 - TIME: 14.3192266 s