
method {:test} Test28() {
expect 8 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(8);
expect r0 >= 0 && r0 * r0 <= 8 < (r0 + 1) * (r0 + 1);
}
method {:test} Test29() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(9);
expect r0 >= 0 && r0 * r0 <= 9 < (r0 + 1) * (r0 + 1);
}
method {:test} Test30() {
expect 783 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(783);
expect r0 >= 0 && r0 * r0 <= 783 < (r0 + 1) * (r0 + 1);
}

// REPEAT 8 - TIME: 15.1054928 s