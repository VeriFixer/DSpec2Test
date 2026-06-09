
method {:test} Test24() {
expect 7 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(7);
expect r0 >= 0 && r0 * r0 <= 7 < (r0 + 1) * (r0 + 1);
}
method {:test} Test25() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(8);
expect r0 >= 0 && r0 * r0 <= 8 < (r0 + 1) * (r0 + 1);
}
method {:test} Test26() {
expect 728 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(728);
expect r0 >= 0 && r0 * r0 <= 728 < (r0 + 1) * (r0 + 1);
}

// REPEAT 7 - TIME: 13.2487455 s