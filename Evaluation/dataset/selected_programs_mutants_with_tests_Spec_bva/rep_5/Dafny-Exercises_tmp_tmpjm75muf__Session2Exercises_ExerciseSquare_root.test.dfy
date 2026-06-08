
method {:test} Test33() {
expect 10404 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10404);
expect r0 >= 0 && r0 * r0 <= 10404 < (r0 + 1) * (r0 + 1);
}
method {:test} Test34() {
expect 10404 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10404);
expect r0 >= 0 && r0 * r0 <= 10404 < (r0 + 1) * (r0 + 1);
}
method {:test} Test35() {
expect 10404 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10404);
expect r0 >= 0 && r0 * r0 <= 10404 < (r0 + 1) * (r0 + 1);
}

// REPEAT 5 - TIME: 18.3248745 s