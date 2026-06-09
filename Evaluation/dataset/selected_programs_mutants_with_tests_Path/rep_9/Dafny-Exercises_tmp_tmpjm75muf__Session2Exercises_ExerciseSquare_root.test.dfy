
method {:test} Test24() {
expect 171 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(171);
expect r0 >= 0 && r0 * r0 <= 171 < (r0 + 1) * (r0 + 1);
}
method {:test} Test25() {
expect 66 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(66);
expect r0 >= 0 && r0 * r0 <= 66 < (r0 + 1) * (r0 + 1);
}
method {:test} Test26() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(8);
expect r0 >= 0 && r0 * r0 <= 8 < (r0 + 1) * (r0 + 1);
}

// REPEAT 9 - TIME: 213.0962412 s