
method {:test} Test15() {
expect 100 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(100);
expect r0 >= 0 && r0 * r0 <= 100 < (r0 + 1) * (r0 + 1);
}
method {:test} Test16() {
expect 25 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(25);
expect r0 >= 0 && r0 * r0 <= 25 < (r0 + 1) * (r0 + 1);
}
method {:test} Test17() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(5);
expect r0 >= 0 && r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}

// REPEAT 6 - TIME: 131.1051985 s