
method {:test} Test9() {
expect 4 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot1(4);
expect r0 >= 0 && r0 * r0 <= 4 < (r0 + 1) * (r0 + 1);
}
method {:test} Test10() {
expect 5 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot2(5);
expect r0 >= 0 && r0 * r0 <= 5 < (r0 + 1) * (r0 + 1);
}
method {:test} Test11() {
expect 3 >= 0, "If this check fails at runtime, the test does not meet the preconditions";
var r0 := mroot3(3);
expect r0 >= 0 && r0 * r0 <= 3 < (r0 + 1) * (r0 + 1);
}

// REPEAT 4 - TIME: 85.572198 s