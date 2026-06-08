
method {:test} Test27() {
expect 256 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(256);
expect r0 >= 0 && r0 * r0 <= 256 < (r0 + 1) * (r0 + 1);
}
method {:test} Test28() {
expect 67 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(67);
expect r0 >= 0 && r0 * r0 <= 67 < (r0 + 1) * (r0 + 1);
}
method {:test} Test29() {
expect 9 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(9);
expect r0 >= 0 && r0 * r0 <= 9 < (r0 + 1) * (r0 + 1);
}

// REPEAT 10 - TIME: 159.2420981 s