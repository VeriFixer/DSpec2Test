
method {:test} Test24() {
expect 35 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(35);
expect r0 >= 0 && r0 * r0 <= 35 < (r0 + 1) * (r0 + 1);
}
method {:test} Test25() {
expect 35 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(35);
expect r0 >= 0 && r0 * r0 <= 35 < (r0 + 1) * (r0 + 1);
}
method {:test} Test26() {
expect 35 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(35);
expect r0 >= 0 && r0 * r0 <= 35 < (r0 + 1) * (r0 + 1);
}

// REPEAT 9 - TIME: 10.2851965 s