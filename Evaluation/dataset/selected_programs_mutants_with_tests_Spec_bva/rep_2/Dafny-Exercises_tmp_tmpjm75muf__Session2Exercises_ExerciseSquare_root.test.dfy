
method {:test} Test24() {
expect 10001 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10001);
expect r0 >= 0 && r0 * r0 <= 10001 < (r0 + 1) * (r0 + 1);
}
method {:test} Test25() {
expect 10001 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10001);
expect r0 >= 0 && r0 * r0 <= 10001 < (r0 + 1) * (r0 + 1);
}
method {:test} Test26() {
expect 10001 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10001);
expect r0 >= 0 && r0 * r0 <= 10001 < (r0 + 1) * (r0 + 1);
}

// REPEAT 2 - TIME: 14.5900174 s