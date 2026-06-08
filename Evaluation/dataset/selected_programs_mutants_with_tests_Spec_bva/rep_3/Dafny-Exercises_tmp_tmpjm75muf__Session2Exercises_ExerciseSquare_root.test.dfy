
method {:test} Test27() {
expect 10200 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(10200);
expect r0 >= 0 && r0 * r0 <= 10200 < (r0 + 1) * (r0 + 1);
}
method {:test} Test28() {
expect 10200 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(10200);
expect r0 >= 0 && r0 * r0 <= 10200 < (r0 + 1) * (r0 + 1);
}
method {:test} Test29() {
expect 10200 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(10200);
expect r0 >= 0 && r0 * r0 <= 10200 < (r0 + 1) * (r0 + 1);
}

// REPEAT 3 - TIME: 15.8922631 s