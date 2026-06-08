
method {:test} Test8() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(3);
expect r0 >= 0 && r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}
method {:test} Test9() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(4);
expect r0 >= 0 && r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}
method {:test} Test10() {
expect 15 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(15);
expect r0 >= 0 && r0 * r0 <= 15 < (r0 + 1) * (r0 + 1);
}
method {:test} Test11() {
expect 143 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(143);
expect r0 >= 0 && r0 * r0 <= 143 < (r0 + 1) * (r0 + 1);
}

// REPEAT 3 - TIME: 6.7706308 s